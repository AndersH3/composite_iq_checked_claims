(** Module: ThreeTestSelectionDecomposition.v
   Purpose: Connect two-stratum association-decomposition identities to
   AB/AC/BC test admissions conditioned on the pass/fail status of the
   remaining third test; derive exact pooling laws and reversal conditions.
   Mathematical representation: Every two-by-two raw selection table is
   represented by four original eight-outcome masses from ThreeTestAdmissions.
   Six selected and nonselected raw tables share the one central mixture
   algebra in library/rocq/TwoStratumAssociation.v. No duplicate probability
   sum, recursive event engine or conditional model is constructed.
   Explicit hypotheses: Original eight-atom masses are nonnegative and sum
   to one; theorems about two conditional rates or their signs require
   positive masses of BOTH selection strata. There is no independence
   assumption and no use of unproved Gaussian or empirical premises.
   Library use: TwoStratumAssociation, ThreeTestAdmissions,
   ThreeTestPairBridge, ThreeTestConditionalStrata and Admissions,
   plus Rocq Stdlib.Reals, Lra, Psatz and Field.
   Limitations: Exact finite three-test event algebra and selection bias
   identities. This is not a trivariate Gaussian conditional law, a normal
   tail numerical certificate or evidence about observed IQ measurements.
   Reproduction: scripts/compile_rocq.sh in pinned Rocq Prover 9.2, after
   both the reusable mixture algebra and the triple-test admissions modules.
   AI disclosure: ChatGPT assisted in generating the documentation and
   proofs; only the pinned Rocq kernel establishes validity.
*)
From Stdlib Require Import Reals Lra Psatz.
Require Import Admissions ThreeTestAdmissions ThreeTestPairBridge
  ThreeTestConditionalStrata TwoStratumAssociation.
Open Scope R_scope.

(**
 [selection_AB_selected_mass] (definition) — Positive-selection stratum mass of the AB admissions pair conditioned on third test C
 Mathematical meaning: Positive-selection stratum mass of the AB admissions pair conditioned on third test C
 Exact declaration: Definition selection_AB_selected_mass (m:ThreeTestModel):R := mix_total_yes mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AB_selected_mass (m:ThreeTestModel):R := mix_total_yes mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).

(**
 [selection_AB_other_mass] (definition) — Negative-selection stratum mass of the AB admissions pair conditioned on third test C
 Mathematical meaning: Negative-selection stratum mass of the AB admissions pair conditioned on third test C
 Exact declaration: Definition selection_AB_other_mass (m:ThreeTestModel):R := mix_total_no mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AB_other_mass (m:ThreeTestModel):R := mix_total_no mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).

(**
 [selection_AB_pooled_association] (definition) — Pooled binary-indicator association for admission routes AB
 Mathematical meaning: Pooled binary-indicator association for admission routes AB
 Exact declaration: Definition selection_AB_pooled_association (m:ThreeTestModel):R := mix_pooled_association mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AB_pooled_association (m:ThreeTestModel):R := mix_pooled_association mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).

(**
 [selection_AB_within_association] (definition) — Within-stratum raw association weighted by complementary selection mass for AB
 Mathematical meaning: Within-stratum raw association weighted by complementary selection mass for AB
 Exact declaration: Definition selection_AB_within_association (m:ThreeTestModel):R := mix_within mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AB_within_association (m:ThreeTestModel):R := mix_within mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).

(**
 [selection_AB_between_association] (definition) — Between-stratum association induced by conditional-marginal shifts of both AB tests
 Mathematical meaning: Between-stratum association induced by conditional-marginal shifts of both AB tests
 Exact declaration: Definition selection_AB_between_association (m:ThreeTestModel):R := mix_between mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AB_between_association (m:ThreeTestModel):R := mix_between mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).

(**
 [selection_AB_first_gap] (definition) — Selected-versus-other first-route marginal pass-rate contrast for AB
 Mathematical meaning: Selected-versus-other first-route marginal pass-rate contrast for AB
 Exact declaration: Definition selection_AB_first_gap (m:ThreeTestModel):R := mix_gap_first mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AB_first_gap (m:ThreeTestModel):R := mix_gap_first mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).

(**
 [selection_AB_second_gap] (definition) — Selected-versus-other second-route marginal pass-rate contrast for AB
 Mathematical meaning: Selected-versus-other second-route marginal pass-rate contrast for AB
 Exact declaration: Definition selection_AB_second_gap (m:ThreeTestModel):R := mix_gap_second mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AB_second_gap (m:ThreeTestModel):R := mix_gap_second mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).

(**
 [selection_AB_selected_mass_correct] (theorem) — The C-pass stratum mass for the AB pair is exactly the third-test pass probability.
 Mathematical meaning: The C-pass stratum mass for the AB pair is exactly the third-test pass probability.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_selected_mass m=pC3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_selected_mass_correct :
  forall m:ThreeTestModel, selection_AB_selected_mass m=pC3 m.
Proof.
  intro m; unfold selection_AB_selected_mass, mix_total_yes; triple_lra.
Qed.

(**
 [selection_AB_other_mass_correct] (theorem) — The C-failure stratum mass for the AB pair is the complement of the third-test pass probability.
 Mathematical meaning: The C-failure stratum mass for the AB pair is the complement of the third-test pass probability.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_other_mass m=1-pC3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_other_mass_correct :
  forall m:ThreeTestModel, selection_AB_other_mass m=1-pC3 m.
Proof.
  intro m; unfold selection_AB_other_mass, mix_total_no; triple_lra.
Qed.

(**
 [selection_AB_selection_partition_unit] (theorem) — The C pass and fail selection groups partition the complete normalized three-test probability space.
 Mathematical meaning: The C pass and fail selection groups partition the complete normalized three-test probability space.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_selected_mass m+selection_AB_other_mass m=1.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_selection_partition_unit :
  forall m:ThreeTestModel, selection_AB_selected_mass m+selection_AB_other_mass m=1.
Proof.
  intro m; rewrite selection_AB_selected_mass_correct, selection_AB_other_mass_correct; ring.
Qed.

(**
 [selection_AB_pooled_association_is_pair] (theorem) — Aggregating C-pass and C-failure cells recovers the original AB two-route cross-product association.
 Mathematical meaning: Aggregating C-pass and C-failure cells recovers the original AB two-route cross-product association.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_pooled_association m=Admissions.admission_association (pair_AB3 m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_pooled_association_is_pair :
  forall m:ThreeTestModel, selection_AB_pooled_association m=Admissions.admission_association (pair_AB3 m).
Proof.
  intro m; unfold selection_AB_pooled_association, mix_pooled_association, Admissions.admission_association, pair_AB3; simpl; ring.
Qed.

(**
 [selection_AB_pooled_covariance_exact] (theorem) — The pooled AB association equals joint admission probability minus the product of original route marginals.
 Mathematical meaning: The pooled AB association equals joint admission probability minus the product of original route marginals.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_pooled_association m=pAB3 m-pA3 m*pB3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_pooled_covariance_exact :
  forall m:ThreeTestModel, selection_AB_pooled_association m=pAB3 m-pA3 m*pB3 m.
Proof.
  intro m; rewrite selection_AB_pooled_association_is_pair; apply triple_ab_association_covariance.
Qed.

(**
 [selection_AB_within_two_stratum_formula] (theorem) — The AB adjusted within association is the selected/other local determinant weighted by the opposite stratum's mass.
 Mathematical meaning: The AB adjusted within association is the selected/other local determinant weighted by the opposite stratum's mass.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_within_association m=selection_AB_other_mass m*mix_local_assoc_yes mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)+selection_AB_selected_mass m*mix_local_assoc_no mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_within_two_stratum_formula :
  forall m:ThreeTestModel, selection_AB_within_association m=selection_AB_other_mass m*mix_local_assoc_yes mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false)+selection_AB_selected_mass m*mix_local_assoc_no mass3 m (true,true,true) mass3 m (true,false,true) mass3 m (false,true,true) mass3 m (false,false,true) mass3 m (true,true,false) mass3 m (true,false,false) mass3 m (false,true,false) mass3 m (false,false,false).
Proof.
  intro m; unfold selection_AB_within_association, selection_AB_selected_mass, selection_AB_other_mass; apply mix_within_explicit.
Qed.

(**
 [selection_AB_between_selection_gap_product] (theorem) — The AB selection-induced association equals the product of first-route and second-route signed conditional-marginal contrasts.
 Mathematical meaning: The AB selection-induced association equals the product of first-route and second-route signed conditional-marginal contrasts.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_between_association m=selection_AB_first_gap m*selection_AB_second_gap m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_between_selection_gap_product :
  forall m:ThreeTestModel, selection_AB_between_association m=selection_AB_first_gap m*selection_AB_second_gap m.
Proof.
  intro m; unfold selection_AB_between_association, selection_AB_first_gap, selection_AB_second_gap; apply mix_between_explicit.
Qed.

(**
 [selection_AB_stratified_factorization] (theorem) — The pooled AB association times the product of selected and other masses exactly splits into weighted within- and between-stratum terms.
 Mathematical meaning: The pooled AB association times the product of selected and other masses exactly splits into weighted within- and between-stratum terms.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_selected_mass m*selection_AB_other_mass m*selection_AB_pooled_association m=(selection_AB_selected_mass m+selection_AB_other_mass m)*selection_AB_within_association m+selection_AB_between_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_stratified_factorization :
  forall m:ThreeTestModel, selection_AB_selected_mass m*selection_AB_other_mass m*selection_AB_pooled_association m=(selection_AB_selected_mass m+selection_AB_other_mass m)*selection_AB_within_association m+selection_AB_between_association m.
Proof.
  intro m; unfold selection_AB_selected_mass, selection_AB_other_mass, selection_AB_pooled_association, selection_AB_within_association, selection_AB_between_association; apply mix_stratified_association_identity.
Qed.

(**
 [selection_AB_unit_mass_decomposition] (theorem) — With full-population normalized selection groups, the pooled AB association has an exact within-plus-between decomposition after multiplying by selected/other mass.
 Mathematical meaning: With full-population normalized selection groups, the pooled AB association has an exact within-plus-between decomposition after multiplying by selected/other mass.
 Exact checked proposition: forall m:ThreeTestModel, selection_AB_selected_mass m*selection_AB_other_mass m*selection_AB_pooled_association m=selection_AB_within_association m+selection_AB_between_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_unit_mass_decomposition :
  forall m:ThreeTestModel, selection_AB_selected_mass m*selection_AB_other_mass m*selection_AB_pooled_association m=selection_AB_within_association m+selection_AB_between_association m.
Proof.
  intro m; pose proof (selection_AB_stratified_factorization m) as Hid.
  rewrite selection_AB_selection_partition_unit in Hid.
  nra.
Qed.

(**
 [selection_AB_positive_iff] (theorem) — Positive pooled dependence for pair AB holds precisely when the selection-adjusted within and between components have positive combined sign.
 Mathematical meaning: Positive pooled dependence for pair AB holds precisely when the selection-adjusted within and between components have positive combined sign.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (0<selection_AB_pooled_association m<->0<selection_AB_within_association m+selection_AB_between_association m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_positive_iff :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (0<selection_AB_pooled_association m<->0<selection_AB_within_association m+selection_AB_between_association m).
Proof.
  intros m Hy Hn.
  pose proof (selection_AB_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AB_negative_iff] (theorem) — Negative pooled dependence for pair AB holds precisely when the within-plus-between sum is negative.
 Mathematical meaning: Negative pooled dependence for pair AB holds precisely when the within-plus-between sum is negative.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (selection_AB_pooled_association m<0<->selection_AB_within_association m+selection_AB_between_association m<0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_negative_iff :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (selection_AB_pooled_association m<0<->selection_AB_within_association m+selection_AB_between_association m<0).
Proof.
  intros m Hy Hn.
  pose proof (selection_AB_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AB_independent_iff] (theorem) — Marginal pairwise independence for AB holds exactly when the adjusted within and between terms cancel.
 Mathematical meaning: Marginal pairwise independence for AB holds exactly when the adjusted within and between terms cancel.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (selection_AB_pooled_association m=0<->selection_AB_within_association m+selection_AB_between_association m=0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_independent_iff :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (selection_AB_pooled_association m=0<->selection_AB_within_association m+selection_AB_between_association m=0).
Proof.
  intros m Hy Hn.
  pose proof (selection_AB_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AB_nonnegative_iff] (theorem) — Nonnegative pooled pairwise association for AB is equivalent to nonnegative adjusted total selection association.
 Mathematical meaning: Nonnegative pooled pairwise association for AB is equivalent to nonnegative adjusted total selection association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (0<=selection_AB_pooled_association m<->0<=selection_AB_within_association m+selection_AB_between_association m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_nonnegative_iff :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (0<=selection_AB_pooled_association m<->0<=selection_AB_within_association m+selection_AB_between_association m).
Proof.
  intros m Hy Hn.
  pose proof (selection_AB_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AB_nonpositive_iff] (theorem) — Nonpositive pooled pairwise association for AB is equivalent to nonpositive adjusted total selection association.
 Mathematical meaning: Nonpositive pooled pairwise association for AB is equivalent to nonpositive adjusted total selection association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (selection_AB_pooled_association m<=0<->selection_AB_within_association m+selection_AB_between_association m<=0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_nonpositive_iff :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (selection_AB_pooled_association m<=0<->selection_AB_within_association m+selection_AB_between_association m<=0).
Proof.
  intros m Hy Hn.
  pose proof (selection_AB_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AB_first_conditional_rate_gap] (theorem) — The first-route pass rate among C-passers minus its rate among C-failers equals the first selection-gap numerator divided by both selection probabilities.
 Mathematical meaning: The first-route pass rate among C-passers minus its rate among C-failers equals the first selection-gap numerator divided by both selection probabilities.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,false,true))/selection_AB_selected_mass m-(mass3 m (true,true,false)+mass3 m (true,false,false))/selection_AB_other_mass m=selection_AB_first_gap m/(selection_AB_selected_mass m*selection_AB_other_mass m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_first_conditional_rate_gap :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,false,true))/selection_AB_selected_mass m-(mass3 m (true,true,false)+mass3 m (true,false,false))/selection_AB_other_mass m=selection_AB_first_gap m/(selection_AB_selected_mass m*selection_AB_other_mass m).
Proof.
  intros m Hy Hn.
  unfold selection_AB_selected_mass, selection_AB_other_mass, selection_AB_first_gap in *.
  apply mix_first_rate_gap_exact; assumption.
Qed.

(**
 [selection_AB_second_conditional_rate_gap] (theorem) — The second-route pass rate among C-passers minus its rate among C-failers equals the second selection-gap numerator divided by both positive selection probabilities.
 Mathematical meaning: The second-route pass rate among C-passers minus its rate among C-failers equals the second selection-gap numerator divided by both positive selection probabilities.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (mass3 m (true,true,true)+mass3 m (false,true,true))/selection_AB_selected_mass m-(mass3 m (true,true,false)+mass3 m (false,true,false))/selection_AB_other_mass m=selection_AB_second_gap m/(selection_AB_selected_mass m*selection_AB_other_mass m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_second_conditional_rate_gap :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> (mass3 m (true,true,true)+mass3 m (false,true,true))/selection_AB_selected_mass m-(mass3 m (true,true,false)+mass3 m (false,true,false))/selection_AB_other_mass m=selection_AB_second_gap m/(selection_AB_selected_mass m*selection_AB_other_mass m).
Proof.
  intros m Hy Hn.
  unfold selection_AB_selected_mass, selection_AB_other_mass, selection_AB_second_gap in *.
  apply mix_second_rate_gap_exact; assumption.
Qed.

(**
 [selection_AB_positive_from_within_and_selection] (theorem) — Positive between-stratum selection dependence dominates a nonnegative within component and forces positive pooled AB association.
 Mathematical meaning: Positive between-stratum selection dependence dominates a nonnegative within component and forces positive pooled AB association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> 0<=selection_AB_within_association m->0<selection_AB_between_association m->0<selection_AB_pooled_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_positive_from_within_and_selection :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> 0<=selection_AB_within_association m->0<selection_AB_between_association m->0<selection_AB_pooled_association m.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AB_positive_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_AB_negative_from_within_and_selection] (theorem) — Negative between-stratum selection dependence dominates a nonpositive within component and forces negative pooled AB association.
 Mathematical meaning: Negative between-stratum selection dependence dominates a nonpositive within component and forces negative pooled AB association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> selection_AB_within_association m<=0->selection_AB_between_association m<0->selection_AB_pooled_association m<0.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_negative_from_within_and_selection :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> selection_AB_within_association m<=0->selection_AB_between_association m<0->selection_AB_pooled_association m<0.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AB_negative_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_AB_simpson_positive_reversal_criterion] (theorem) — If both-selection mixture has negative within association, a sufficiently positive between effect can reverse the pooled AB association to positive.
 Mathematical meaning: If both-selection mixture has negative within association, a sufficiently positive between effect can reverse the pooled AB association to positive.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> selection_AB_within_association m<0->-selection_AB_within_association m<selection_AB_between_association m->0<selection_AB_pooled_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_simpson_positive_reversal_criterion :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> selection_AB_within_association m<0->-selection_AB_within_association m<selection_AB_between_association m->0<selection_AB_pooled_association m.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AB_positive_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_AB_simpson_negative_reversal_criterion] (theorem) — If both-selection mixture has positive within association, a sufficiently negative between effect can reverse pooled AB association to negative.
 Mathematical meaning: If both-selection mixture has positive within association, a sufficiently negative between effect can reverse pooled AB association to negative.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> 0<selection_AB_within_association m->selection_AB_between_association m<-selection_AB_within_association m->selection_AB_pooled_association m<0.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AB_simpson_negative_reversal_criterion :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m -> 0<selection_AB_other_mass m -> 0<selection_AB_within_association m->selection_AB_between_association m<-selection_AB_within_association m->selection_AB_pooled_association m<0.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AB_negative_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_AC_selected_mass] (definition) — Positive-selection stratum mass of the AC admissions pair conditioned on third test B
 Mathematical meaning: Positive-selection stratum mass of the AC admissions pair conditioned on third test B
 Exact declaration: Definition selection_AC_selected_mass (m:ThreeTestModel):R := mix_total_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AC_selected_mass (m:ThreeTestModel):R := mix_total_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_AC_other_mass] (definition) — Negative-selection stratum mass of the AC admissions pair conditioned on third test B
 Mathematical meaning: Negative-selection stratum mass of the AC admissions pair conditioned on third test B
 Exact declaration: Definition selection_AC_other_mass (m:ThreeTestModel):R := mix_total_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AC_other_mass (m:ThreeTestModel):R := mix_total_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_AC_pooled_association] (definition) — Pooled binary-indicator association for admission routes AC
 Mathematical meaning: Pooled binary-indicator association for admission routes AC
 Exact declaration: Definition selection_AC_pooled_association (m:ThreeTestModel):R := mix_pooled_association mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AC_pooled_association (m:ThreeTestModel):R := mix_pooled_association mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_AC_within_association] (definition) — Within-stratum raw association weighted by complementary selection mass for AC
 Mathematical meaning: Within-stratum raw association weighted by complementary selection mass for AC
 Exact declaration: Definition selection_AC_within_association (m:ThreeTestModel):R := mix_within mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AC_within_association (m:ThreeTestModel):R := mix_within mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_AC_between_association] (definition) — Between-stratum association induced by conditional-marginal shifts of both AC tests
 Mathematical meaning: Between-stratum association induced by conditional-marginal shifts of both AC tests
 Exact declaration: Definition selection_AC_between_association (m:ThreeTestModel):R := mix_between mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AC_between_association (m:ThreeTestModel):R := mix_between mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_AC_first_gap] (definition) — Selected-versus-other first-route marginal pass-rate contrast for AC
 Mathematical meaning: Selected-versus-other first-route marginal pass-rate contrast for AC
 Exact declaration: Definition selection_AC_first_gap (m:ThreeTestModel):R := mix_gap_first mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AC_first_gap (m:ThreeTestModel):R := mix_gap_first mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_AC_second_gap] (definition) — Selected-versus-other second-route marginal pass-rate contrast for AC
 Mathematical meaning: Selected-versus-other second-route marginal pass-rate contrast for AC
 Exact declaration: Definition selection_AC_second_gap (m:ThreeTestModel):R := mix_gap_second mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_AC_second_gap (m:ThreeTestModel):R := mix_gap_second mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_AC_selected_mass_correct] (theorem) — The B-pass stratum mass for the AC pair is exactly the third-test pass probability.
 Mathematical meaning: The B-pass stratum mass for the AC pair is exactly the third-test pass probability.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_selected_mass m=pB3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_selected_mass_correct :
  forall m:ThreeTestModel, selection_AC_selected_mass m=pB3 m.
Proof.
  intro m; unfold selection_AC_selected_mass, mix_total_yes; triple_lra.
Qed.

(**
 [selection_AC_other_mass_correct] (theorem) — The B-failure stratum mass for the AC pair is the complement of the third-test pass probability.
 Mathematical meaning: The B-failure stratum mass for the AC pair is the complement of the third-test pass probability.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_other_mass m=1-pB3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_other_mass_correct :
  forall m:ThreeTestModel, selection_AC_other_mass m=1-pB3 m.
Proof.
  intro m; unfold selection_AC_other_mass, mix_total_no; triple_lra.
Qed.

(**
 [selection_AC_selection_partition_unit] (theorem) — The B pass and fail selection groups partition the complete normalized three-test probability space.
 Mathematical meaning: The B pass and fail selection groups partition the complete normalized three-test probability space.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_selected_mass m+selection_AC_other_mass m=1.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_selection_partition_unit :
  forall m:ThreeTestModel, selection_AC_selected_mass m+selection_AC_other_mass m=1.
Proof.
  intro m; rewrite selection_AC_selected_mass_correct, selection_AC_other_mass_correct; ring.
Qed.

(**
 [selection_AC_pooled_association_is_pair] (theorem) — Aggregating B-pass and B-failure cells recovers the original AC two-route cross-product association.
 Mathematical meaning: Aggregating B-pass and B-failure cells recovers the original AC two-route cross-product association.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_pooled_association m=Admissions.admission_association (pair_AC3 m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_pooled_association_is_pair :
  forall m:ThreeTestModel, selection_AC_pooled_association m=Admissions.admission_association (pair_AC3 m).
Proof.
  intro m; unfold selection_AC_pooled_association, mix_pooled_association, Admissions.admission_association, pair_AC3; simpl; ring.
Qed.

(**
 [selection_AC_pooled_covariance_exact] (theorem) — The pooled AC association equals joint admission probability minus the product of original route marginals.
 Mathematical meaning: The pooled AC association equals joint admission probability minus the product of original route marginals.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_pooled_association m=pAC3 m-pA3 m*pC3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_pooled_covariance_exact :
  forall m:ThreeTestModel, selection_AC_pooled_association m=pAC3 m-pA3 m*pC3 m.
Proof.
  intro m; rewrite selection_AC_pooled_association_is_pair; apply triple_ac_association_covariance.
Qed.

(**
 [selection_AC_within_two_stratum_formula] (theorem) — The AC adjusted within association is the selected/other local determinant weighted by the opposite stratum's mass.
 Mathematical meaning: The AC adjusted within association is the selected/other local determinant weighted by the opposite stratum's mass.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_within_association m=selection_AC_other_mass m*mix_local_assoc_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)+selection_AC_selected_mass m*mix_local_assoc_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_within_two_stratum_formula :
  forall m:ThreeTestModel, selection_AC_within_association m=selection_AC_other_mass m*mix_local_assoc_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false)+selection_AC_selected_mass m*mix_local_assoc_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,false,true) mass3 m (false,false,false).
Proof.
  intro m; unfold selection_AC_within_association, selection_AC_selected_mass, selection_AC_other_mass; apply mix_within_explicit.
Qed.

(**
 [selection_AC_between_selection_gap_product] (theorem) — The AC selection-induced association equals the product of first-route and second-route signed conditional-marginal contrasts.
 Mathematical meaning: The AC selection-induced association equals the product of first-route and second-route signed conditional-marginal contrasts.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_between_association m=selection_AC_first_gap m*selection_AC_second_gap m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_between_selection_gap_product :
  forall m:ThreeTestModel, selection_AC_between_association m=selection_AC_first_gap m*selection_AC_second_gap m.
Proof.
  intro m; unfold selection_AC_between_association, selection_AC_first_gap, selection_AC_second_gap; apply mix_between_explicit.
Qed.

(**
 [selection_AC_stratified_factorization] (theorem) — The pooled AC association times the product of selected and other masses exactly splits into weighted within- and between-stratum terms.
 Mathematical meaning: The pooled AC association times the product of selected and other masses exactly splits into weighted within- and between-stratum terms.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_selected_mass m*selection_AC_other_mass m*selection_AC_pooled_association m=(selection_AC_selected_mass m+selection_AC_other_mass m)*selection_AC_within_association m+selection_AC_between_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_stratified_factorization :
  forall m:ThreeTestModel, selection_AC_selected_mass m*selection_AC_other_mass m*selection_AC_pooled_association m=(selection_AC_selected_mass m+selection_AC_other_mass m)*selection_AC_within_association m+selection_AC_between_association m.
Proof.
  intro m; unfold selection_AC_selected_mass, selection_AC_other_mass, selection_AC_pooled_association, selection_AC_within_association, selection_AC_between_association; apply mix_stratified_association_identity.
Qed.

(**
 [selection_AC_unit_mass_decomposition] (theorem) — With full-population normalized selection groups, the pooled AC association has an exact within-plus-between decomposition after multiplying by selected/other mass.
 Mathematical meaning: With full-population normalized selection groups, the pooled AC association has an exact within-plus-between decomposition after multiplying by selected/other mass.
 Exact checked proposition: forall m:ThreeTestModel, selection_AC_selected_mass m*selection_AC_other_mass m*selection_AC_pooled_association m=selection_AC_within_association m+selection_AC_between_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_unit_mass_decomposition :
  forall m:ThreeTestModel, selection_AC_selected_mass m*selection_AC_other_mass m*selection_AC_pooled_association m=selection_AC_within_association m+selection_AC_between_association m.
Proof.
  intro m; pose proof (selection_AC_stratified_factorization m) as Hid.
  rewrite selection_AC_selection_partition_unit in Hid.
  nra.
Qed.

(**
 [selection_AC_positive_iff] (theorem) — Positive pooled dependence for pair AC holds precisely when the selection-adjusted within and between components have positive combined sign.
 Mathematical meaning: Positive pooled dependence for pair AC holds precisely when the selection-adjusted within and between components have positive combined sign.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (0<selection_AC_pooled_association m<->0<selection_AC_within_association m+selection_AC_between_association m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_positive_iff :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (0<selection_AC_pooled_association m<->0<selection_AC_within_association m+selection_AC_between_association m).
Proof.
  intros m Hy Hn.
  pose proof (selection_AC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AC_negative_iff] (theorem) — Negative pooled dependence for pair AC holds precisely when the within-plus-between sum is negative.
 Mathematical meaning: Negative pooled dependence for pair AC holds precisely when the within-plus-between sum is negative.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (selection_AC_pooled_association m<0<->selection_AC_within_association m+selection_AC_between_association m<0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_negative_iff :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (selection_AC_pooled_association m<0<->selection_AC_within_association m+selection_AC_between_association m<0).
Proof.
  intros m Hy Hn.
  pose proof (selection_AC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AC_independent_iff] (theorem) — Marginal pairwise independence for AC holds exactly when the adjusted within and between terms cancel.
 Mathematical meaning: Marginal pairwise independence for AC holds exactly when the adjusted within and between terms cancel.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (selection_AC_pooled_association m=0<->selection_AC_within_association m+selection_AC_between_association m=0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_independent_iff :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (selection_AC_pooled_association m=0<->selection_AC_within_association m+selection_AC_between_association m=0).
Proof.
  intros m Hy Hn.
  pose proof (selection_AC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AC_nonnegative_iff] (theorem) — Nonnegative pooled pairwise association for AC is equivalent to nonnegative adjusted total selection association.
 Mathematical meaning: Nonnegative pooled pairwise association for AC is equivalent to nonnegative adjusted total selection association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (0<=selection_AC_pooled_association m<->0<=selection_AC_within_association m+selection_AC_between_association m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_nonnegative_iff :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (0<=selection_AC_pooled_association m<->0<=selection_AC_within_association m+selection_AC_between_association m).
Proof.
  intros m Hy Hn.
  pose proof (selection_AC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AC_nonpositive_iff] (theorem) — Nonpositive pooled pairwise association for AC is equivalent to nonpositive adjusted total selection association.
 Mathematical meaning: Nonpositive pooled pairwise association for AC is equivalent to nonpositive adjusted total selection association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (selection_AC_pooled_association m<=0<->selection_AC_within_association m+selection_AC_between_association m<=0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_nonpositive_iff :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (selection_AC_pooled_association m<=0<->selection_AC_within_association m+selection_AC_between_association m<=0).
Proof.
  intros m Hy Hn.
  pose proof (selection_AC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_AC_first_conditional_rate_gap] (theorem) — The first-route pass rate among B-passers minus its rate among B-failers equals the first selection-gap numerator divided by both selection probabilities.
 Mathematical meaning: The first-route pass rate among B-passers minus its rate among B-failers equals the first selection-gap numerator divided by both selection probabilities.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,true,false))/selection_AC_selected_mass m-(mass3 m (true,false,true)+mass3 m (true,false,false))/selection_AC_other_mass m=selection_AC_first_gap m/(selection_AC_selected_mass m*selection_AC_other_mass m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_first_conditional_rate_gap :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,true,false))/selection_AC_selected_mass m-(mass3 m (true,false,true)+mass3 m (true,false,false))/selection_AC_other_mass m=selection_AC_first_gap m/(selection_AC_selected_mass m*selection_AC_other_mass m).
Proof.
  intros m Hy Hn.
  unfold selection_AC_selected_mass, selection_AC_other_mass, selection_AC_first_gap in *.
  apply mix_first_rate_gap_exact; assumption.
Qed.

(**
 [selection_AC_second_conditional_rate_gap] (theorem) — The second-route pass rate among B-passers minus its rate among B-failers equals the second selection-gap numerator divided by both positive selection probabilities.
 Mathematical meaning: The second-route pass rate among B-passers minus its rate among B-failers equals the second selection-gap numerator divided by both positive selection probabilities.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (mass3 m (true,true,true)+mass3 m (false,true,true))/selection_AC_selected_mass m-(mass3 m (true,false,true)+mass3 m (false,false,true))/selection_AC_other_mass m=selection_AC_second_gap m/(selection_AC_selected_mass m*selection_AC_other_mass m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_second_conditional_rate_gap :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> (mass3 m (true,true,true)+mass3 m (false,true,true))/selection_AC_selected_mass m-(mass3 m (true,false,true)+mass3 m (false,false,true))/selection_AC_other_mass m=selection_AC_second_gap m/(selection_AC_selected_mass m*selection_AC_other_mass m).
Proof.
  intros m Hy Hn.
  unfold selection_AC_selected_mass, selection_AC_other_mass, selection_AC_second_gap in *.
  apply mix_second_rate_gap_exact; assumption.
Qed.

(**
 [selection_AC_positive_from_within_and_selection] (theorem) — Positive between-stratum selection dependence dominates a nonnegative within component and forces positive pooled AC association.
 Mathematical meaning: Positive between-stratum selection dependence dominates a nonnegative within component and forces positive pooled AC association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> 0<=selection_AC_within_association m->0<selection_AC_between_association m->0<selection_AC_pooled_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_positive_from_within_and_selection :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> 0<=selection_AC_within_association m->0<selection_AC_between_association m->0<selection_AC_pooled_association m.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AC_positive_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_AC_negative_from_within_and_selection] (theorem) — Negative between-stratum selection dependence dominates a nonpositive within component and forces negative pooled AC association.
 Mathematical meaning: Negative between-stratum selection dependence dominates a nonpositive within component and forces negative pooled AC association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> selection_AC_within_association m<=0->selection_AC_between_association m<0->selection_AC_pooled_association m<0.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_negative_from_within_and_selection :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> selection_AC_within_association m<=0->selection_AC_between_association m<0->selection_AC_pooled_association m<0.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AC_negative_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_AC_simpson_positive_reversal_criterion] (theorem) — If both-selection mixture has negative within association, a sufficiently positive between effect can reverse the pooled AC association to positive.
 Mathematical meaning: If both-selection mixture has negative within association, a sufficiently positive between effect can reverse the pooled AC association to positive.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> selection_AC_within_association m<0->-selection_AC_within_association m<selection_AC_between_association m->0<selection_AC_pooled_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_simpson_positive_reversal_criterion :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> selection_AC_within_association m<0->-selection_AC_within_association m<selection_AC_between_association m->0<selection_AC_pooled_association m.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AC_positive_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_AC_simpson_negative_reversal_criterion] (theorem) — If both-selection mixture has positive within association, a sufficiently negative between effect can reverse pooled AC association to negative.
 Mathematical meaning: If both-selection mixture has positive within association, a sufficiently negative between effect can reverse pooled AC association to negative.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> 0<selection_AC_within_association m->selection_AC_between_association m<-selection_AC_within_association m->selection_AC_pooled_association m<0.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_AC_simpson_negative_reversal_criterion :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m -> 0<selection_AC_other_mass m -> 0<selection_AC_within_association m->selection_AC_between_association m<-selection_AC_within_association m->selection_AC_pooled_association m<0.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_AC_negative_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_BC_selected_mass] (definition) — Positive-selection stratum mass of the BC admissions pair conditioned on third test A
 Mathematical meaning: Positive-selection stratum mass of the BC admissions pair conditioned on third test A
 Exact declaration: Definition selection_BC_selected_mass (m:ThreeTestModel):R := mix_total_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_BC_selected_mass (m:ThreeTestModel):R := mix_total_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_BC_other_mass] (definition) — Negative-selection stratum mass of the BC admissions pair conditioned on third test A
 Mathematical meaning: Negative-selection stratum mass of the BC admissions pair conditioned on third test A
 Exact declaration: Definition selection_BC_other_mass (m:ThreeTestModel):R := mix_total_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_BC_other_mass (m:ThreeTestModel):R := mix_total_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_BC_pooled_association] (definition) — Pooled binary-indicator association for admission routes BC
 Mathematical meaning: Pooled binary-indicator association for admission routes BC
 Exact declaration: Definition selection_BC_pooled_association (m:ThreeTestModel):R := mix_pooled_association mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_BC_pooled_association (m:ThreeTestModel):R := mix_pooled_association mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_BC_within_association] (definition) — Within-stratum raw association weighted by complementary selection mass for BC
 Mathematical meaning: Within-stratum raw association weighted by complementary selection mass for BC
 Exact declaration: Definition selection_BC_within_association (m:ThreeTestModel):R := mix_within mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_BC_within_association (m:ThreeTestModel):R := mix_within mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_BC_between_association] (definition) — Between-stratum association induced by conditional-marginal shifts of both BC tests
 Mathematical meaning: Between-stratum association induced by conditional-marginal shifts of both BC tests
 Exact declaration: Definition selection_BC_between_association (m:ThreeTestModel):R := mix_between mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_BC_between_association (m:ThreeTestModel):R := mix_between mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_BC_first_gap] (definition) — Selected-versus-other first-route marginal pass-rate contrast for BC
 Mathematical meaning: Selected-versus-other first-route marginal pass-rate contrast for BC
 Exact declaration: Definition selection_BC_first_gap (m:ThreeTestModel):R := mix_gap_first mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_BC_first_gap (m:ThreeTestModel):R := mix_gap_first mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_BC_second_gap] (definition) — Selected-versus-other second-route marginal pass-rate contrast for BC
 Mathematical meaning: Selected-versus-other second-route marginal pass-rate contrast for BC
 Exact declaration: Definition selection_BC_second_gap (m:ThreeTestModel):R := mix_gap_second mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)..
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Transparent application of the unique generic TwoStratumAssociation algebra to the two four-atom selected raw tables.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Definition selection_BC_second_gap (m:ThreeTestModel):R := mix_gap_second mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).

(**
 [selection_BC_selected_mass_correct] (theorem) — The A-pass stratum mass for the BC pair is exactly the third-test pass probability.
 Mathematical meaning: The A-pass stratum mass for the BC pair is exactly the third-test pass probability.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_selected_mass m=pA3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_selected_mass_correct :
  forall m:ThreeTestModel, selection_BC_selected_mass m=pA3 m.
Proof.
  intro m; unfold selection_BC_selected_mass, mix_total_yes; triple_lra.
Qed.

(**
 [selection_BC_other_mass_correct] (theorem) — The A-failure stratum mass for the BC pair is the complement of the third-test pass probability.
 Mathematical meaning: The A-failure stratum mass for the BC pair is the complement of the third-test pass probability.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_other_mass m=1-pA3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_other_mass_correct :
  forall m:ThreeTestModel, selection_BC_other_mass m=1-pA3 m.
Proof.
  intro m; unfold selection_BC_other_mass, mix_total_no; triple_lra.
Qed.

(**
 [selection_BC_selection_partition_unit] (theorem) — The A pass and fail selection groups partition the complete normalized three-test probability space.
 Mathematical meaning: The A pass and fail selection groups partition the complete normalized three-test probability space.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_selected_mass m+selection_BC_other_mass m=1.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_selection_partition_unit :
  forall m:ThreeTestModel, selection_BC_selected_mass m+selection_BC_other_mass m=1.
Proof.
  intro m; rewrite selection_BC_selected_mass_correct, selection_BC_other_mass_correct; ring.
Qed.

(**
 [selection_BC_pooled_association_is_pair] (theorem) — Aggregating A-pass and A-failure cells recovers the original BC two-route cross-product association.
 Mathematical meaning: Aggregating A-pass and A-failure cells recovers the original BC two-route cross-product association.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_pooled_association m=Admissions.admission_association (pair_BC3 m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_pooled_association_is_pair :
  forall m:ThreeTestModel, selection_BC_pooled_association m=Admissions.admission_association (pair_BC3 m).
Proof.
  intro m; unfold selection_BC_pooled_association, mix_pooled_association, Admissions.admission_association, pair_BC3; simpl; ring.
Qed.

(**
 [selection_BC_pooled_covariance_exact] (theorem) — The pooled BC association equals joint admission probability minus the product of original route marginals.
 Mathematical meaning: The pooled BC association equals joint admission probability minus the product of original route marginals.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_pooled_association m=pBC3 m-pB3 m*pC3 m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_pooled_covariance_exact :
  forall m:ThreeTestModel, selection_BC_pooled_association m=pBC3 m-pB3 m*pC3 m.
Proof.
  intro m; rewrite selection_BC_pooled_association_is_pair; apply triple_bc_association_covariance.
Qed.

(**
 [selection_BC_within_two_stratum_formula] (theorem) — The BC adjusted within association is the selected/other local determinant weighted by the opposite stratum's mass.
 Mathematical meaning: The BC adjusted within association is the selected/other local determinant weighted by the opposite stratum's mass.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_within_association m=selection_BC_other_mass m*mix_local_assoc_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)+selection_BC_selected_mass m*mix_local_assoc_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_within_two_stratum_formula :
  forall m:ThreeTestModel, selection_BC_within_association m=selection_BC_other_mass m*mix_local_assoc_yes mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false)+selection_BC_selected_mass m*mix_local_assoc_no mass3 m (true,true,true) mass3 m (true,true,false) mass3 m (true,false,true) mass3 m (true,false,false) mass3 m (false,true,true) mass3 m (false,true,false) mass3 m (false,false,true) mass3 m (false,false,false).
Proof.
  intro m; unfold selection_BC_within_association, selection_BC_selected_mass, selection_BC_other_mass; apply mix_within_explicit.
Qed.

(**
 [selection_BC_between_selection_gap_product] (theorem) — The BC selection-induced association equals the product of first-route and second-route signed conditional-marginal contrasts.
 Mathematical meaning: The BC selection-induced association equals the product of first-route and second-route signed conditional-marginal contrasts.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_between_association m=selection_BC_first_gap m*selection_BC_second_gap m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_between_selection_gap_product :
  forall m:ThreeTestModel, selection_BC_between_association m=selection_BC_first_gap m*selection_BC_second_gap m.
Proof.
  intro m; unfold selection_BC_between_association, selection_BC_first_gap, selection_BC_second_gap; apply mix_between_explicit.
Qed.

(**
 [selection_BC_stratified_factorization] (theorem) — The pooled BC association times the product of selected and other masses exactly splits into weighted within- and between-stratum terms.
 Mathematical meaning: The pooled BC association times the product of selected and other masses exactly splits into weighted within- and between-stratum terms.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_selected_mass m*selection_BC_other_mass m*selection_BC_pooled_association m=(selection_BC_selected_mass m+selection_BC_other_mass m)*selection_BC_within_association m+selection_BC_between_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_stratified_factorization :
  forall m:ThreeTestModel, selection_BC_selected_mass m*selection_BC_other_mass m*selection_BC_pooled_association m=(selection_BC_selected_mass m+selection_BC_other_mass m)*selection_BC_within_association m+selection_BC_between_association m.
Proof.
  intro m; unfold selection_BC_selected_mass, selection_BC_other_mass, selection_BC_pooled_association, selection_BC_within_association, selection_BC_between_association; apply mix_stratified_association_identity.
Qed.

(**
 [selection_BC_unit_mass_decomposition] (theorem) — With full-population normalized selection groups, the pooled BC association has an exact within-plus-between decomposition after multiplying by selected/other mass.
 Mathematical meaning: With full-population normalized selection groups, the pooled BC association has an exact within-plus-between decomposition after multiplying by selected/other mass.
 Exact checked proposition: forall m:ThreeTestModel, selection_BC_selected_mass m*selection_BC_other_mass m*selection_BC_pooled_association m=selection_BC_within_association m+selection_BC_between_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_unit_mass_decomposition :
  forall m:ThreeTestModel, selection_BC_selected_mass m*selection_BC_other_mass m*selection_BC_pooled_association m=selection_BC_within_association m+selection_BC_between_association m.
Proof.
  intro m; pose proof (selection_BC_stratified_factorization m) as Hid.
  rewrite selection_BC_selection_partition_unit in Hid.
  nra.
Qed.

(**
 [selection_BC_positive_iff] (theorem) — Positive pooled dependence for pair BC holds precisely when the selection-adjusted within and between components have positive combined sign.
 Mathematical meaning: Positive pooled dependence for pair BC holds precisely when the selection-adjusted within and between components have positive combined sign.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (0<selection_BC_pooled_association m<->0<selection_BC_within_association m+selection_BC_between_association m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_positive_iff :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (0<selection_BC_pooled_association m<->0<selection_BC_within_association m+selection_BC_between_association m).
Proof.
  intros m Hy Hn.
  pose proof (selection_BC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_BC_negative_iff] (theorem) — Negative pooled dependence for pair BC holds precisely when the within-plus-between sum is negative.
 Mathematical meaning: Negative pooled dependence for pair BC holds precisely when the within-plus-between sum is negative.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (selection_BC_pooled_association m<0<->selection_BC_within_association m+selection_BC_between_association m<0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_negative_iff :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (selection_BC_pooled_association m<0<->selection_BC_within_association m+selection_BC_between_association m<0).
Proof.
  intros m Hy Hn.
  pose proof (selection_BC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_BC_independent_iff] (theorem) — Marginal pairwise independence for BC holds exactly when the adjusted within and between terms cancel.
 Mathematical meaning: Marginal pairwise independence for BC holds exactly when the adjusted within and between terms cancel.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (selection_BC_pooled_association m=0<->selection_BC_within_association m+selection_BC_between_association m=0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_independent_iff :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (selection_BC_pooled_association m=0<->selection_BC_within_association m+selection_BC_between_association m=0).
Proof.
  intros m Hy Hn.
  pose proof (selection_BC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_BC_nonnegative_iff] (theorem) — Nonnegative pooled pairwise association for BC is equivalent to nonnegative adjusted total selection association.
 Mathematical meaning: Nonnegative pooled pairwise association for BC is equivalent to nonnegative adjusted total selection association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (0<=selection_BC_pooled_association m<->0<=selection_BC_within_association m+selection_BC_between_association m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_nonnegative_iff :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (0<=selection_BC_pooled_association m<->0<=selection_BC_within_association m+selection_BC_between_association m).
Proof.
  intros m Hy Hn.
  pose proof (selection_BC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_BC_nonpositive_iff] (theorem) — Nonpositive pooled pairwise association for BC is equivalent to nonpositive adjusted total selection association.
 Mathematical meaning: Nonpositive pooled pairwise association for BC is equivalent to nonpositive adjusted total selection association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (selection_BC_pooled_association m<=0<->selection_BC_within_association m+selection_BC_between_association m<=0).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_nonpositive_iff :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (selection_BC_pooled_association m<=0<->selection_BC_within_association m+selection_BC_between_association m<=0).
Proof.
  intros m Hy Hn.
  pose proof (selection_BC_unit_mass_decomposition m) as Hid.
  assert (Hp:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro H; nra.
Qed.

(**
 [selection_BC_first_conditional_rate_gap] (theorem) — The first-route pass rate among A-passers minus its rate among A-failers equals the first selection-gap numerator divided by both selection probabilities.
 Mathematical meaning: The first-route pass rate among A-passers minus its rate among A-failers equals the first selection-gap numerator divided by both selection probabilities.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,true,false))/selection_BC_selected_mass m-(mass3 m (false,true,true)+mass3 m (false,true,false))/selection_BC_other_mass m=selection_BC_first_gap m/(selection_BC_selected_mass m*selection_BC_other_mass m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_first_conditional_rate_gap :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,true,false))/selection_BC_selected_mass m-(mass3 m (false,true,true)+mass3 m (false,true,false))/selection_BC_other_mass m=selection_BC_first_gap m/(selection_BC_selected_mass m*selection_BC_other_mass m).
Proof.
  intros m Hy Hn.
  unfold selection_BC_selected_mass, selection_BC_other_mass, selection_BC_first_gap in *.
  apply mix_first_rate_gap_exact; assumption.
Qed.

(**
 [selection_BC_second_conditional_rate_gap] (theorem) — The second-route pass rate among A-passers minus its rate among A-failers equals the second selection-gap numerator divided by both positive selection probabilities.
 Mathematical meaning: The second-route pass rate among A-passers minus its rate among A-failers equals the second selection-gap numerator divided by both positive selection probabilities.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,false,true))/selection_BC_selected_mass m-(mass3 m (false,true,true)+mass3 m (false,false,true))/selection_BC_other_mass m=selection_BC_second_gap m/(selection_BC_selected_mass m*selection_BC_other_mass m).
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_second_conditional_rate_gap :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> (mass3 m (true,true,true)+mass3 m (true,false,true))/selection_BC_selected_mass m-(mass3 m (false,true,true)+mass3 m (false,false,true))/selection_BC_other_mass m=selection_BC_second_gap m/(selection_BC_selected_mass m*selection_BC_other_mass m).
Proof.
  intros m Hy Hn.
  unfold selection_BC_selected_mass, selection_BC_other_mass, selection_BC_second_gap in *.
  apply mix_second_rate_gap_exact; assumption.
Qed.

(**
 [selection_BC_positive_from_within_and_selection] (theorem) — Positive between-stratum selection dependence dominates a nonnegative within component and forces positive pooled BC association.
 Mathematical meaning: Positive between-stratum selection dependence dominates a nonnegative within component and forces positive pooled BC association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> 0<=selection_BC_within_association m->0<selection_BC_between_association m->0<selection_BC_pooled_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_positive_from_within_and_selection :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> 0<=selection_BC_within_association m->0<selection_BC_between_association m->0<selection_BC_pooled_association m.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_BC_positive_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_BC_negative_from_within_and_selection] (theorem) — Negative between-stratum selection dependence dominates a nonpositive within component and forces negative pooled BC association.
 Mathematical meaning: Negative between-stratum selection dependence dominates a nonpositive within component and forces negative pooled BC association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> selection_BC_within_association m<=0->selection_BC_between_association m<0->selection_BC_pooled_association m<0.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_negative_from_within_and_selection :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> selection_BC_within_association m<=0->selection_BC_between_association m<0->selection_BC_pooled_association m<0.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_BC_negative_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_BC_simpson_positive_reversal_criterion] (theorem) — If both-selection mixture has negative within association, a sufficiently positive between effect can reverse the pooled BC association to positive.
 Mathematical meaning: If both-selection mixture has negative within association, a sufficiently positive between effect can reverse the pooled BC association to positive.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> selection_BC_within_association m<0->-selection_BC_within_association m<selection_BC_between_association m->0<selection_BC_pooled_association m.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_simpson_positive_reversal_criterion :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> selection_BC_within_association m<0->-selection_BC_within_association m<selection_BC_between_association m->0<selection_BC_pooled_association m.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_BC_positive_iff m Hy Hn)).
  nra.
Qed.

(**
 [selection_BC_simpson_negative_reversal_criterion] (theorem) — If both-selection mixture has positive within association, a sufficiently negative between effect can reverse pooled BC association to negative.
 Mathematical meaning: If both-selection mixture has positive within association, a sufficiently negative between effect can reverse pooled BC association to negative.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> 0<selection_BC_within_association m->selection_BC_between_association m<-selection_BC_within_association m->selection_BC_pooled_association m<0.
 Premises and side conditions: The source is the eight-atom nonnegative
 unit-normalized ThreeTestModel. Polynomial event identities require no
 extra premise; rates and positivity comparisons between selected and
 nonselected test takers explicitly require strictly positive masses
 of both selection groups. Independence is never assumed implicitly.
 Proof/definition method: Reduce to the kernel-checked TwoStratumAssociation identities, the ThreeTestAdmissions finite eight-atom enumeration, and the already checked pairwise Admissions covariance bridge, with Stdlib.Lra/Psatz/Ring.
 Library reuse: TwoStratumAssociation, FiniteUnion.finite_prob and
 FiniteSum.finite_sum through ThreeTestAdmissions, Admissions.TwoEventModel
 through ThreeTestPairBridge, and Stdlib real-algebra tactics.
 Boundary: Exact finite Boolean admissions selection and Simpson-effect
 algebra only, not Gaussian conditional distributions, empirical
 psychometrics, or continuous multivariate normal tails.
*)
Theorem selection_BC_simpson_negative_reversal_criterion :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m -> 0<selection_BC_other_mass m -> 0<selection_BC_within_association m->selection_BC_between_association m<-selection_BC_within_association m->selection_BC_pooled_association m<0.
Proof.
  intros m Hy Hn Hw Hb.
  apply (proj2 (selection_BC_negative_iff m Hy Hn)).
  nra.
Qed.

