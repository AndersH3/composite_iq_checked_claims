(** Module: ThreeTestReversalCriteria.v
 Purpose: State exact necessary, sufficient, and sharp conditions for
 Simpson-style association reversal in the Towers three-test admissions
 model, with explicit strata and conditional independence premises.
 Mathematical representation: For each of the pairs AB, AC and BC, group
 eight Boolean atom masses into third-test-pass and third-test-fail tables.
 Conditional association is represented by selected raw cross-products.
 The pooled determinant's sign is controlled by the within/between terms
 from the earlier checked selection decomposition.
 Explicit hypotheses: Nonnegative normalized atomic masses are encoded
 in ThreeTestModel. Strata must have strictly positive mass for sign
 equivalences and conditional independences. All zero/local signs and
 selection-gap hypotheses are stated inside the corresponding theorem.
 Library use: ThreeTestAdmissions, ThreeTestSelectionDecomposition,
 TwoStratumReversal, TwoStratumAssociation, Admissions and the existing
 FiniteSum / FiniteUnion probability implementation. Proof tactics use
 only Rocq Stdlib.Reals, Lra, Psatz and standard integral-domain lemmas.
 Limitations: Results describe exact finite binary admission events,
 not a Gaussian conditional law, normal tail integration, or empirical
 test correlation. No inference of IQ population parameters is supplied.
 Reproduction: Rocq 9.2 with scripts/compile_rocq.sh, after the generic
 reversal and Towers multiple-test selection algebra modules.
 AI disclosure: OpenAI ChatGPT assisted with statement generation, proofs,
 comments and structural refactoring. Successful Rocq compilation is
 necessary to assert that each exact stated theorem has been proved.
*)
From Stdlib Require Import Reals Lra Psatz.
Require Import Admissions ThreeTestAdmissions ThreeTestSelectionDecomposition
  TwoStratumAssociation TwoStratumReversal.
Open Scope R_scope.

(**
 [reversal_AB_selected_raw_association] (definition) — The unnormalized concordant-minus-discordant association of AB inside the omitted-test C-pass stratum.
 Mathematical meaning: The unnormalized concordant-minus-discordant association of AB inside the omitted-test C-pass stratum.
 Exact declaration: Definition reversal_AB_selected_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,true))*(mass3 m (false,false,true))-(mass3 m (true,false,true))*(mass3 m (false,true,true)).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: A four-atom raw determinant using the existing ThreeTestModel mass function; no custom probability aggregate.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Definition reversal_AB_selected_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,true))*(mass3 m (false,false,true))-(mass3 m (true,false,true))*(mass3 m (false,true,true)).

(**
 [reversal_AB_other_raw_association] (definition) — The corresponding unnormalized AB association among C nonpassers.
 Mathematical meaning: The corresponding unnormalized AB association among C nonpassers.
 Exact declaration: Definition reversal_AB_other_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,false))*(mass3 m (false,false,false))-(mass3 m (true,false,false))*(mass3 m (false,true,false)).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: A four-atom raw determinant using the existing ThreeTestModel mass function; no custom probability aggregate.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Definition reversal_AB_other_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,false))*(mass3 m (false,false,false))-(mass3 m (true,false,false))*(mass3 m (false,true,false)).

(**
 [reversal_AB_pooled_positive_iff_sharp_threshold] (theorem) — Pooled AB dependence is positive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AB dependence is positive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (0<selection_AB_pooled_association m <-> - selection_AB_within_association m < selection_AB_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_pooled_positive_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (0<selection_AB_pooled_association m <-> - selection_AB_within_association m < selection_AB_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_pooled_negative_iff_sharp_threshold] (theorem) — Pooled AB dependence is negative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AB dependence is negative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (selection_AB_pooled_association m<0 <-> selection_AB_between_association m < - selection_AB_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_pooled_negative_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (selection_AB_pooled_association m<0 <-> selection_AB_between_association m < - selection_AB_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_pooled_zero_iff_sharp_threshold] (theorem) — Pooled AB dependence is zero exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AB dependence is zero exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (selection_AB_pooled_association m=0 <-> selection_AB_between_association m = - selection_AB_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_pooled_zero_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (selection_AB_pooled_association m=0 <-> selection_AB_between_association m = - selection_AB_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_pooled_nonnegative_iff_sharp_threshold] (theorem) — Pooled AB dependence is nonnegative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AB dependence is nonnegative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (0<=selection_AB_pooled_association m <-> - selection_AB_within_association m <= selection_AB_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_pooled_nonnegative_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (0<=selection_AB_pooled_association m <-> - selection_AB_within_association m <= selection_AB_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_pooled_nonpositive_iff_sharp_threshold] (theorem) — Pooled AB dependence is nonpositive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AB dependence is nonpositive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (selection_AB_pooled_association m<=0 <-> selection_AB_between_association m <= - selection_AB_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_pooled_nonpositive_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> (selection_AB_pooled_association m<=0 <-> selection_AB_between_association m <= - selection_AB_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_within_pooled_positive_iff_between_positive] (theorem) — If conditional AB association cancels exactly across the two strata, the positive pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AB association cancels exactly across the two strata, the positive pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (0<selection_AB_pooled_association m<->0<selection_AB_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_within_pooled_positive_iff_between_positive :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (0<selection_AB_pooled_association m<->0<selection_AB_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_within_pooled_negative_iff_between_negative] (theorem) — If conditional AB association cancels exactly across the two strata, the negative pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AB association cancels exactly across the two strata, the negative pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (selection_AB_pooled_association m<0<->selection_AB_between_association m<0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_within_pooled_negative_iff_between_negative :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (selection_AB_pooled_association m<0<->selection_AB_between_association m<0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_within_pooled_zero_iff_between_zero] (theorem) — If conditional AB association cancels exactly across the two strata, the zero pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AB association cancels exactly across the two strata, the zero pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (selection_AB_pooled_association m=0<->selection_AB_between_association m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_within_pooled_zero_iff_between_zero :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (selection_AB_pooled_association m=0<->selection_AB_between_association m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_within_pooled_nonnegative_iff_between_nonnegative] (theorem) — If conditional AB association cancels exactly across the two strata, the nonnegative pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AB association cancels exactly across the two strata, the nonnegative pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (0<=selection_AB_pooled_association m<->0<=selection_AB_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_within_pooled_nonnegative_iff_between_nonnegative :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (0<=selection_AB_pooled_association m<->0<=selection_AB_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_within_pooled_nonpositive_iff_between_nonpositive] (theorem) — If conditional AB association cancels exactly across the two strata, the nonpositive pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AB association cancels exactly across the two strata, the nonpositive pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (selection_AB_pooled_association m<=0<->selection_AB_between_association m<=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_within_pooled_nonpositive_iff_between_nonpositive :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_within_association m=0 -> (selection_AB_pooled_association m<=0<->selection_AB_between_association m<=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_between_pooled_positive_iff_within_positive] (theorem) — When selection does not induce between-stratum AB association, positive pooled dependence is exactly positive weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AB association, positive pooled dependence is exactly positive weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (0<selection_AB_pooled_association m<->0<selection_AB_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_between_pooled_positive_iff_within_positive :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (0<selection_AB_pooled_association m<->0<selection_AB_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_between_pooled_negative_iff_within_negative] (theorem) — When selection does not induce between-stratum AB association, negative pooled dependence is exactly negative weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AB association, negative pooled dependence is exactly negative weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (selection_AB_pooled_association m<0<->selection_AB_within_association m<0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_between_pooled_negative_iff_within_negative :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (selection_AB_pooled_association m<0<->selection_AB_within_association m<0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_between_pooled_zero_iff_within_zero] (theorem) — When selection does not induce between-stratum AB association, zero pooled dependence is exactly zero weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AB association, zero pooled dependence is exactly zero weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (selection_AB_pooled_association m=0<->selection_AB_within_association m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_between_pooled_zero_iff_within_zero :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (selection_AB_pooled_association m=0<->selection_AB_within_association m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_between_pooled_nonnegative_iff_within_nonnegative] (theorem) — When selection does not induce between-stratum AB association, nonnegative pooled dependence is exactly nonnegative weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AB association, nonnegative pooled dependence is exactly nonnegative weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (0<=selection_AB_pooled_association m<->0<=selection_AB_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_between_pooled_nonnegative_iff_within_nonnegative :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (0<=selection_AB_pooled_association m<->0<=selection_AB_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_zero_between_pooled_nonpositive_iff_within_nonpositive] (theorem) — When selection does not induce between-stratum AB association, nonpositive pooled dependence is exactly nonpositive weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AB association, nonpositive pooled dependence is exactly nonpositive weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (selection_AB_pooled_association m<=0<->selection_AB_within_association m<=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_zero_between_pooled_nonpositive_iff_within_nonpositive :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_between_association m=0 -> (selection_AB_pooled_association m<=0<->selection_AB_within_association m<=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AB_within_raw_contingency_cells] (theorem) — The unnormalized AB within-stratum association is an exact positive-mass weighted sum of selected and nonselected four-cell determinants.
 Mathematical meaning: The unnormalized AB within-stratum association is an exact positive-mass weighted sum of selected and nonselected four-cell determinants.
 Exact checked proposition: forall m:ThreeTestModel,  selection_AB_within_association m=selection_AB_other_mass m*reversal_AB_selected_raw_association m+selection_AB_selected_mass m*reversal_AB_other_raw_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_within_raw_contingency_cells :
  forall m:ThreeTestModel,  selection_AB_within_association m=selection_AB_other_mass m*reversal_AB_selected_raw_association m+selection_AB_selected_mass m*reversal_AB_other_raw_association m.
Proof.
  intro m.
  unfold selection_AB_within_association, selection_AB_selected_mass, selection_AB_other_mass, reversal_AB_selected_raw_association, reversal_AB_other_raw_association.
  apply mix_within_explicit.
Qed.

(**
 [reversal_AB_both_strata_independent_within_zero] (theorem) — Conditional independence of AB in both positive- and negative-C subpopulations makes the within association vanish.
 Mathematical meaning: Conditional independence of AB in both positive- and negative-C subpopulations makes the within association vanish.
 Exact checked proposition: forall m:ThreeTestModel,  reversal_AB_selected_raw_association m=0 -> reversal_AB_other_raw_association m=0 -> selection_AB_within_association m=0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_both_strata_independent_within_zero :
  forall m:ThreeTestModel,  reversal_AB_selected_raw_association m=0 -> reversal_AB_other_raw_association m=0 -> selection_AB_within_association m=0.
Proof.
  intros m Hy Hn.
  rewrite reversal_AB_within_raw_contingency_cells.
  rewrite Hy,Hn; ring.
Qed.

(**
 [reversal_AB_conditional_independence_pooled_iff_selection_gap_zero] (theorem) — Under AB independence in both C strata, the population tests are independent precisely when either admission route has no selection-marginal gap.
 Mathematical meaning: Under AB independence in both C strata, the population tests are independent precisely when either admission route has no selection-marginal gap.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m=0 -> reversal_AB_other_raw_association m=0 -> (selection_AB_pooled_association m=0 <-> selection_AB_first_gap m=0 \/ selection_AB_second_gap m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_conditional_independence_pooled_iff_selection_gap_zero :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m=0 -> reversal_AB_other_raw_association m=0 -> (selection_AB_pooled_association m=0 <-> selection_AB_first_gap m=0 \/ selection_AB_second_gap m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn.
  pose proof (reversal_AB_both_strata_independent_within_zero m Hy Hn) as Hw.
  pose proof (selection_AB_between_selection_gap_product m) as Hg.
  rewrite Hw, Hg in Hmix.
  split.
  - intro Hp.
    assert (Hzero:selection_AB_first_gap m*selection_AB_second_gap m=0) by nra.
    apply Rmult_integral in Hzero; exact Hzero.
  - intros [Ha|Hb]; rewrite Ha in Hmix || rewrite Hb in Hmix; nra.
Qed.

(**
 [reversal_AB_both_local_negative_within_negative] (theorem) — Strictly negative conditional AB association in both C pass/fail groups produces strictly negative weighted within-stratum association.
 Mathematical meaning: Strictly negative conditional AB association in both C pass/fail groups produces strictly negative weighted within-stratum association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m<0 -> reversal_AB_other_raw_association m<0 -> selection_AB_within_association m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_both_local_negative_within_negative :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m<0 -> reversal_AB_other_raw_association m<0 -> selection_AB_within_association m<0.
Proof.
  intros m Hu Hv Hy Hn.
  rewrite reversal_AB_within_raw_contingency_cells.
  nra.
Qed.

(**
 [reversal_AB_both_local_positive_within_positive] (theorem) — Strictly positive conditional AB association in both C pass/fail groups produces strictly positive weighted within-stratum association.
 Mathematical meaning: Strictly positive conditional AB association in both C pass/fail groups produces strictly positive weighted within-stratum association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> 0<reversal_AB_selected_raw_association m -> 0<reversal_AB_other_raw_association m -> 0<selection_AB_within_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_both_local_positive_within_positive :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> 0<reversal_AB_selected_raw_association m -> 0<reversal_AB_other_raw_association m -> 0<selection_AB_within_association m.
Proof.
  intros m Hu Hv Hy Hn.
  rewrite reversal_AB_within_raw_contingency_cells.
  nra.
Qed.

(**
 [reversal_AB_positive_simpson_reversal_needs_positive_between] (theorem) — Positive pooled AB association despite negative association within both C strata necessarily requires positive between-stratum selection dependence.
 Mathematical meaning: Positive pooled AB association despite negative association within both C strata necessarily requires positive between-stratum selection dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m<0 -> reversal_AB_other_raw_association m<0 -> 0<selection_AB_pooled_association m -> 0<selection_AB_between_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_positive_simpson_reversal_needs_positive_between :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m<0 -> reversal_AB_other_raw_association m<0 -> 0<selection_AB_pooled_association m -> 0<selection_AB_between_association m.
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn Hp.
  pose proof (reversal_AB_both_local_negative_within_negative m Hu Hv Hy Hn) as Hw.
  nra.
Qed.

(**
 [reversal_AB_negative_simpson_reversal_needs_negative_between] (theorem) — Negative pooled AB association despite positive association within both C strata necessarily requires negative between-stratum selection dependence.
 Mathematical meaning: Negative pooled AB association despite positive association within both C strata necessarily requires negative between-stratum selection dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> 0<reversal_AB_selected_raw_association m -> 0<reversal_AB_other_raw_association m -> selection_AB_pooled_association m<0 -> selection_AB_between_association m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_negative_simpson_reversal_needs_negative_between :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> 0<reversal_AB_selected_raw_association m -> 0<reversal_AB_other_raw_association m -> selection_AB_pooled_association m<0 -> selection_AB_between_association m<0.
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn Hp.
  pose proof (reversal_AB_both_local_positive_within_positive m Hu Hv Hy Hn) as Hw.
  nra.
Qed.

(**
 [reversal_AB_positive_reversal_needs_aligned_selection_gaps] (theorem) — Positive AB Simpson reversal from two negatively associated C strata requires a positive product of the route-specific selected-versus-nonselected pass-rate gaps.
 Mathematical meaning: Positive AB Simpson reversal from two negatively associated C strata requires a positive product of the route-specific selected-versus-nonselected pass-rate gaps.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m<0 -> reversal_AB_other_raw_association m<0 -> 0<selection_AB_pooled_association m -> 0<selection_AB_first_gap m*selection_AB_second_gap m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_positive_reversal_needs_aligned_selection_gaps :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> reversal_AB_selected_raw_association m<0 -> reversal_AB_other_raw_association m<0 -> 0<selection_AB_pooled_association m -> 0<selection_AB_first_gap m*selection_AB_second_gap m.
Proof.
  intros m Hu Hv Hy Hn Hp.
  pose proof (reversal_AB_positive_simpson_reversal_needs_positive_between m Hu Hv Hy Hn Hp) as Hb.
  rewrite (selection_AB_between_selection_gap_product m) in Hb.
  exact Hb.
Qed.

(**
 [reversal_AB_negative_reversal_needs_opposing_selection_gaps] (theorem) — Negative AB Simpson reversal from two positively associated C strata requires opposite-signed marginal-selection gaps, giving a negative gap product.
 Mathematical meaning: Negative AB Simpson reversal from two positively associated C strata requires opposite-signed marginal-selection gaps, giving a negative gap product.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> 0<reversal_AB_selected_raw_association m -> 0<reversal_AB_other_raw_association m -> selection_AB_pooled_association m<0 -> selection_AB_first_gap m*selection_AB_second_gap m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_negative_reversal_needs_opposing_selection_gaps :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> 0<reversal_AB_selected_raw_association m -> 0<reversal_AB_other_raw_association m -> selection_AB_pooled_association m<0 -> selection_AB_first_gap m*selection_AB_second_gap m<0.
Proof.
  intros m Hu Hv Hy Hn Hp.
  pose proof (reversal_AB_negative_simpson_reversal_needs_negative_between m Hu Hv Hy Hn Hp) as Hb.
  rewrite (selection_AB_between_selection_gap_product m) in Hb.
  exact Hb.
Qed.

(**
 [reversal_AB_equal_first_selection_gap_preserves_nonpositive_within] (theorem) — When the AB first-route admission rate does not vary between C groups, nonpositive within-stratum dependence guarantees nonpositive pooled dependence.
 Mathematical meaning: When the AB first-route admission rate does not vary between C groups, nonpositive within-stratum dependence guarantees nonpositive pooled dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_first_gap m=0 -> selection_AB_within_association m<=0 -> selection_AB_pooled_association m<=0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AB_equal_first_selection_gap_preserves_nonpositive_within :
  forall m:ThreeTestModel, 0<selection_AB_selected_mass m->0<selection_AB_other_mass m-> selection_AB_first_gap m=0 -> selection_AB_within_association m<=0 -> selection_AB_pooled_association m<=0.
Proof.
  intros m Hu Hv.
  pose proof (selection_AB_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AB_selected_mass m*selection_AB_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hg Hw.
  pose proof (selection_AB_between_selection_gap_product m) as Hfactor.
  rewrite Hg in Hfactor.
  assert (Hbetween:selection_AB_between_association m=0) by nra.
  rewrite Hbetween in Hmix; nra.
Qed.

(**
 [reversal_AC_selected_raw_association] (definition) — The unnormalized concordant-minus-discordant association of AC inside the omitted-test B-pass stratum.
 Mathematical meaning: The unnormalized concordant-minus-discordant association of AC inside the omitted-test B-pass stratum.
 Exact declaration: Definition reversal_AC_selected_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,true))*(mass3 m (false,true,false))-(mass3 m (true,true,false))*(mass3 m (false,true,true)).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: A four-atom raw determinant using the existing ThreeTestModel mass function; no custom probability aggregate.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Definition reversal_AC_selected_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,true))*(mass3 m (false,true,false))-(mass3 m (true,true,false))*(mass3 m (false,true,true)).

(**
 [reversal_AC_other_raw_association] (definition) — The corresponding unnormalized AC association among B nonpassers.
 Mathematical meaning: The corresponding unnormalized AC association among B nonpassers.
 Exact declaration: Definition reversal_AC_other_raw_association (m:ThreeTestModel): R := (mass3 m (true,false,true))*(mass3 m (false,false,false))-(mass3 m (true,false,false))*(mass3 m (false,false,true)).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: A four-atom raw determinant using the existing ThreeTestModel mass function; no custom probability aggregate.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Definition reversal_AC_other_raw_association (m:ThreeTestModel): R := (mass3 m (true,false,true))*(mass3 m (false,false,false))-(mass3 m (true,false,false))*(mass3 m (false,false,true)).

(**
 [reversal_AC_pooled_positive_iff_sharp_threshold] (theorem) — Pooled AC dependence is positive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AC dependence is positive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (0<selection_AC_pooled_association m <-> - selection_AC_within_association m < selection_AC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_pooled_positive_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (0<selection_AC_pooled_association m <-> - selection_AC_within_association m < selection_AC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_pooled_negative_iff_sharp_threshold] (theorem) — Pooled AC dependence is negative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AC dependence is negative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (selection_AC_pooled_association m<0 <-> selection_AC_between_association m < - selection_AC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_pooled_negative_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (selection_AC_pooled_association m<0 <-> selection_AC_between_association m < - selection_AC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_pooled_zero_iff_sharp_threshold] (theorem) — Pooled AC dependence is zero exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AC dependence is zero exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (selection_AC_pooled_association m=0 <-> selection_AC_between_association m = - selection_AC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_pooled_zero_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (selection_AC_pooled_association m=0 <-> selection_AC_between_association m = - selection_AC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_pooled_nonnegative_iff_sharp_threshold] (theorem) — Pooled AC dependence is nonnegative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AC dependence is nonnegative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (0<=selection_AC_pooled_association m <-> - selection_AC_within_association m <= selection_AC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_pooled_nonnegative_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (0<=selection_AC_pooled_association m <-> - selection_AC_within_association m <= selection_AC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_pooled_nonpositive_iff_sharp_threshold] (theorem) — Pooled AC dependence is nonpositive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled AC dependence is nonpositive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (selection_AC_pooled_association m<=0 <-> selection_AC_between_association m <= - selection_AC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_pooled_nonpositive_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> (selection_AC_pooled_association m<=0 <-> selection_AC_between_association m <= - selection_AC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_within_pooled_positive_iff_between_positive] (theorem) — If conditional AC association cancels exactly across the two strata, the positive pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AC association cancels exactly across the two strata, the positive pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (0<selection_AC_pooled_association m<->0<selection_AC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_within_pooled_positive_iff_between_positive :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (0<selection_AC_pooled_association m<->0<selection_AC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_within_pooled_negative_iff_between_negative] (theorem) — If conditional AC association cancels exactly across the two strata, the negative pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AC association cancels exactly across the two strata, the negative pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (selection_AC_pooled_association m<0<->selection_AC_between_association m<0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_within_pooled_negative_iff_between_negative :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (selection_AC_pooled_association m<0<->selection_AC_between_association m<0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_within_pooled_zero_iff_between_zero] (theorem) — If conditional AC association cancels exactly across the two strata, the zero pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AC association cancels exactly across the two strata, the zero pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (selection_AC_pooled_association m=0<->selection_AC_between_association m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_within_pooled_zero_iff_between_zero :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (selection_AC_pooled_association m=0<->selection_AC_between_association m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_within_pooled_nonnegative_iff_between_nonnegative] (theorem) — If conditional AC association cancels exactly across the two strata, the nonnegative pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AC association cancels exactly across the two strata, the nonnegative pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (0<=selection_AC_pooled_association m<->0<=selection_AC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_within_pooled_nonnegative_iff_between_nonnegative :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (0<=selection_AC_pooled_association m<->0<=selection_AC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_within_pooled_nonpositive_iff_between_nonpositive] (theorem) — If conditional AC association cancels exactly across the two strata, the nonpositive pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional AC association cancels exactly across the two strata, the nonpositive pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (selection_AC_pooled_association m<=0<->selection_AC_between_association m<=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_within_pooled_nonpositive_iff_between_nonpositive :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_within_association m=0 -> (selection_AC_pooled_association m<=0<->selection_AC_between_association m<=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_between_pooled_positive_iff_within_positive] (theorem) — When selection does not induce between-stratum AC association, positive pooled dependence is exactly positive weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AC association, positive pooled dependence is exactly positive weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (0<selection_AC_pooled_association m<->0<selection_AC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_between_pooled_positive_iff_within_positive :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (0<selection_AC_pooled_association m<->0<selection_AC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_between_pooled_negative_iff_within_negative] (theorem) — When selection does not induce between-stratum AC association, negative pooled dependence is exactly negative weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AC association, negative pooled dependence is exactly negative weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (selection_AC_pooled_association m<0<->selection_AC_within_association m<0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_between_pooled_negative_iff_within_negative :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (selection_AC_pooled_association m<0<->selection_AC_within_association m<0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_between_pooled_zero_iff_within_zero] (theorem) — When selection does not induce between-stratum AC association, zero pooled dependence is exactly zero weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AC association, zero pooled dependence is exactly zero weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (selection_AC_pooled_association m=0<->selection_AC_within_association m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_between_pooled_zero_iff_within_zero :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (selection_AC_pooled_association m=0<->selection_AC_within_association m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_between_pooled_nonnegative_iff_within_nonnegative] (theorem) — When selection does not induce between-stratum AC association, nonnegative pooled dependence is exactly nonnegative weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AC association, nonnegative pooled dependence is exactly nonnegative weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (0<=selection_AC_pooled_association m<->0<=selection_AC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_between_pooled_nonnegative_iff_within_nonnegative :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (0<=selection_AC_pooled_association m<->0<=selection_AC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_zero_between_pooled_nonpositive_iff_within_nonpositive] (theorem) — When selection does not induce between-stratum AC association, nonpositive pooled dependence is exactly nonpositive weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum AC association, nonpositive pooled dependence is exactly nonpositive weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (selection_AC_pooled_association m<=0<->selection_AC_within_association m<=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_zero_between_pooled_nonpositive_iff_within_nonpositive :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_between_association m=0 -> (selection_AC_pooled_association m<=0<->selection_AC_within_association m<=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_AC_within_raw_contingency_cells] (theorem) — The unnormalized AC within-stratum association is an exact positive-mass weighted sum of selected and nonselected four-cell determinants.
 Mathematical meaning: The unnormalized AC within-stratum association is an exact positive-mass weighted sum of selected and nonselected four-cell determinants.
 Exact checked proposition: forall m:ThreeTestModel,  selection_AC_within_association m=selection_AC_other_mass m*reversal_AC_selected_raw_association m+selection_AC_selected_mass m*reversal_AC_other_raw_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_within_raw_contingency_cells :
  forall m:ThreeTestModel,  selection_AC_within_association m=selection_AC_other_mass m*reversal_AC_selected_raw_association m+selection_AC_selected_mass m*reversal_AC_other_raw_association m.
Proof.
  intro m.
  unfold selection_AC_within_association, selection_AC_selected_mass, selection_AC_other_mass, reversal_AC_selected_raw_association, reversal_AC_other_raw_association.
  apply mix_within_explicit.
Qed.

(**
 [reversal_AC_both_strata_independent_within_zero] (theorem) — Conditional independence of AC in both positive- and negative-B subpopulations makes the within association vanish.
 Mathematical meaning: Conditional independence of AC in both positive- and negative-B subpopulations makes the within association vanish.
 Exact checked proposition: forall m:ThreeTestModel,  reversal_AC_selected_raw_association m=0 -> reversal_AC_other_raw_association m=0 -> selection_AC_within_association m=0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_both_strata_independent_within_zero :
  forall m:ThreeTestModel,  reversal_AC_selected_raw_association m=0 -> reversal_AC_other_raw_association m=0 -> selection_AC_within_association m=0.
Proof.
  intros m Hy Hn.
  rewrite reversal_AC_within_raw_contingency_cells.
  rewrite Hy,Hn; ring.
Qed.

(**
 [reversal_AC_conditional_independence_pooled_iff_selection_gap_zero] (theorem) — Under AC independence in both B strata, the population tests are independent precisely when either admission route has no selection-marginal gap.
 Mathematical meaning: Under AC independence in both B strata, the population tests are independent precisely when either admission route has no selection-marginal gap.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m=0 -> reversal_AC_other_raw_association m=0 -> (selection_AC_pooled_association m=0 <-> selection_AC_first_gap m=0 \/ selection_AC_second_gap m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_conditional_independence_pooled_iff_selection_gap_zero :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m=0 -> reversal_AC_other_raw_association m=0 -> (selection_AC_pooled_association m=0 <-> selection_AC_first_gap m=0 \/ selection_AC_second_gap m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn.
  pose proof (reversal_AC_both_strata_independent_within_zero m Hy Hn) as Hw.
  pose proof (selection_AC_between_selection_gap_product m) as Hg.
  rewrite Hw, Hg in Hmix.
  split.
  - intro Hp.
    assert (Hzero:selection_AC_first_gap m*selection_AC_second_gap m=0) by nra.
    apply Rmult_integral in Hzero; exact Hzero.
  - intros [Ha|Hb]; rewrite Ha in Hmix || rewrite Hb in Hmix; nra.
Qed.

(**
 [reversal_AC_both_local_negative_within_negative] (theorem) — Strictly negative conditional AC association in both B pass/fail groups produces strictly negative weighted within-stratum association.
 Mathematical meaning: Strictly negative conditional AC association in both B pass/fail groups produces strictly negative weighted within-stratum association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m<0 -> reversal_AC_other_raw_association m<0 -> selection_AC_within_association m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_both_local_negative_within_negative :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m<0 -> reversal_AC_other_raw_association m<0 -> selection_AC_within_association m<0.
Proof.
  intros m Hu Hv Hy Hn.
  rewrite reversal_AC_within_raw_contingency_cells.
  nra.
Qed.

(**
 [reversal_AC_both_local_positive_within_positive] (theorem) — Strictly positive conditional AC association in both B pass/fail groups produces strictly positive weighted within-stratum association.
 Mathematical meaning: Strictly positive conditional AC association in both B pass/fail groups produces strictly positive weighted within-stratum association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> 0<reversal_AC_selected_raw_association m -> 0<reversal_AC_other_raw_association m -> 0<selection_AC_within_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_both_local_positive_within_positive :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> 0<reversal_AC_selected_raw_association m -> 0<reversal_AC_other_raw_association m -> 0<selection_AC_within_association m.
Proof.
  intros m Hu Hv Hy Hn.
  rewrite reversal_AC_within_raw_contingency_cells.
  nra.
Qed.

(**
 [reversal_AC_positive_simpson_reversal_needs_positive_between] (theorem) — Positive pooled AC association despite negative association within both B strata necessarily requires positive between-stratum selection dependence.
 Mathematical meaning: Positive pooled AC association despite negative association within both B strata necessarily requires positive between-stratum selection dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m<0 -> reversal_AC_other_raw_association m<0 -> 0<selection_AC_pooled_association m -> 0<selection_AC_between_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_positive_simpson_reversal_needs_positive_between :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m<0 -> reversal_AC_other_raw_association m<0 -> 0<selection_AC_pooled_association m -> 0<selection_AC_between_association m.
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn Hp.
  pose proof (reversal_AC_both_local_negative_within_negative m Hu Hv Hy Hn) as Hw.
  nra.
Qed.

(**
 [reversal_AC_negative_simpson_reversal_needs_negative_between] (theorem) — Negative pooled AC association despite positive association within both B strata necessarily requires negative between-stratum selection dependence.
 Mathematical meaning: Negative pooled AC association despite positive association within both B strata necessarily requires negative between-stratum selection dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> 0<reversal_AC_selected_raw_association m -> 0<reversal_AC_other_raw_association m -> selection_AC_pooled_association m<0 -> selection_AC_between_association m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_negative_simpson_reversal_needs_negative_between :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> 0<reversal_AC_selected_raw_association m -> 0<reversal_AC_other_raw_association m -> selection_AC_pooled_association m<0 -> selection_AC_between_association m<0.
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn Hp.
  pose proof (reversal_AC_both_local_positive_within_positive m Hu Hv Hy Hn) as Hw.
  nra.
Qed.

(**
 [reversal_AC_positive_reversal_needs_aligned_selection_gaps] (theorem) — Positive AC Simpson reversal from two negatively associated B strata requires a positive product of the route-specific selected-versus-nonselected pass-rate gaps.
 Mathematical meaning: Positive AC Simpson reversal from two negatively associated B strata requires a positive product of the route-specific selected-versus-nonselected pass-rate gaps.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m<0 -> reversal_AC_other_raw_association m<0 -> 0<selection_AC_pooled_association m -> 0<selection_AC_first_gap m*selection_AC_second_gap m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_positive_reversal_needs_aligned_selection_gaps :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> reversal_AC_selected_raw_association m<0 -> reversal_AC_other_raw_association m<0 -> 0<selection_AC_pooled_association m -> 0<selection_AC_first_gap m*selection_AC_second_gap m.
Proof.
  intros m Hu Hv Hy Hn Hp.
  pose proof (reversal_AC_positive_simpson_reversal_needs_positive_between m Hu Hv Hy Hn Hp) as Hb.
  rewrite (selection_AC_between_selection_gap_product m) in Hb.
  exact Hb.
Qed.

(**
 [reversal_AC_negative_reversal_needs_opposing_selection_gaps] (theorem) — Negative AC Simpson reversal from two positively associated B strata requires opposite-signed marginal-selection gaps, giving a negative gap product.
 Mathematical meaning: Negative AC Simpson reversal from two positively associated B strata requires opposite-signed marginal-selection gaps, giving a negative gap product.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> 0<reversal_AC_selected_raw_association m -> 0<reversal_AC_other_raw_association m -> selection_AC_pooled_association m<0 -> selection_AC_first_gap m*selection_AC_second_gap m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_negative_reversal_needs_opposing_selection_gaps :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> 0<reversal_AC_selected_raw_association m -> 0<reversal_AC_other_raw_association m -> selection_AC_pooled_association m<0 -> selection_AC_first_gap m*selection_AC_second_gap m<0.
Proof.
  intros m Hu Hv Hy Hn Hp.
  pose proof (reversal_AC_negative_simpson_reversal_needs_negative_between m Hu Hv Hy Hn Hp) as Hb.
  rewrite (selection_AC_between_selection_gap_product m) in Hb.
  exact Hb.
Qed.

(**
 [reversal_AC_equal_first_selection_gap_preserves_nonpositive_within] (theorem) — When the AC first-route admission rate does not vary between B groups, nonpositive within-stratum dependence guarantees nonpositive pooled dependence.
 Mathematical meaning: When the AC first-route admission rate does not vary between B groups, nonpositive within-stratum dependence guarantees nonpositive pooled dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_first_gap m=0 -> selection_AC_within_association m<=0 -> selection_AC_pooled_association m<=0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_AC_equal_first_selection_gap_preserves_nonpositive_within :
  forall m:ThreeTestModel, 0<selection_AC_selected_mass m->0<selection_AC_other_mass m-> selection_AC_first_gap m=0 -> selection_AC_within_association m<=0 -> selection_AC_pooled_association m<=0.
Proof.
  intros m Hu Hv.
  pose proof (selection_AC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_AC_selected_mass m*selection_AC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hg Hw.
  pose proof (selection_AC_between_selection_gap_product m) as Hfactor.
  rewrite Hg in Hfactor.
  assert (Hbetween:selection_AC_between_association m=0) by nra.
  rewrite Hbetween in Hmix; nra.
Qed.

(**
 [reversal_BC_selected_raw_association] (definition) — The unnormalized concordant-minus-discordant association of BC inside the omitted-test A-pass stratum.
 Mathematical meaning: The unnormalized concordant-minus-discordant association of BC inside the omitted-test A-pass stratum.
 Exact declaration: Definition reversal_BC_selected_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,true))*(mass3 m (true,false,false))-(mass3 m (true,true,false))*(mass3 m (true,false,true)).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: A four-atom raw determinant using the existing ThreeTestModel mass function; no custom probability aggregate.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Definition reversal_BC_selected_raw_association (m:ThreeTestModel): R := (mass3 m (true,true,true))*(mass3 m (true,false,false))-(mass3 m (true,true,false))*(mass3 m (true,false,true)).

(**
 [reversal_BC_other_raw_association] (definition) — The corresponding unnormalized BC association among A nonpassers.
 Mathematical meaning: The corresponding unnormalized BC association among A nonpassers.
 Exact declaration: Definition reversal_BC_other_raw_association (m:ThreeTestModel): R := (mass3 m (false,true,true))*(mass3 m (false,false,false))-(mass3 m (false,true,false))*(mass3 m (false,false,true)).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: A four-atom raw determinant using the existing ThreeTestModel mass function; no custom probability aggregate.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Definition reversal_BC_other_raw_association (m:ThreeTestModel): R := (mass3 m (false,true,true))*(mass3 m (false,false,false))-(mass3 m (false,true,false))*(mass3 m (false,false,true)).

(**
 [reversal_BC_pooled_positive_iff_sharp_threshold] (theorem) — Pooled BC dependence is positive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled BC dependence is positive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (0<selection_BC_pooled_association m <-> - selection_BC_within_association m < selection_BC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_pooled_positive_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (0<selection_BC_pooled_association m <-> - selection_BC_within_association m < selection_BC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_pooled_negative_iff_sharp_threshold] (theorem) — Pooled BC dependence is negative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled BC dependence is negative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (selection_BC_pooled_association m<0 <-> selection_BC_between_association m < - selection_BC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_pooled_negative_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (selection_BC_pooled_association m<0 <-> selection_BC_between_association m < - selection_BC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_pooled_zero_iff_sharp_threshold] (theorem) — Pooled BC dependence is zero exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled BC dependence is zero exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (selection_BC_pooled_association m=0 <-> selection_BC_between_association m = - selection_BC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_pooled_zero_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (selection_BC_pooled_association m=0 <-> selection_BC_between_association m = - selection_BC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_pooled_nonnegative_iff_sharp_threshold] (theorem) — Pooled BC dependence is nonnegative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled BC dependence is nonnegative exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (0<=selection_BC_pooled_association m <-> - selection_BC_within_association m <= selection_BC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_pooled_nonnegative_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (0<=selection_BC_pooled_association m <-> - selection_BC_within_association m <= selection_BC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_pooled_nonpositive_iff_sharp_threshold] (theorem) — Pooled BC dependence is nonpositive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Mathematical meaning: Pooled BC dependence is nonpositive exactly when the third-test selection association crosses the sharp negative within-stratum threshold.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (selection_BC_pooled_association m<=0 <-> selection_BC_between_association m <= - selection_BC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_pooled_nonpositive_iff_sharp_threshold :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> (selection_BC_pooled_association m<=0 <-> selection_BC_between_association m <= - selection_BC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_within_pooled_positive_iff_between_positive] (theorem) — If conditional BC association cancels exactly across the two strata, the positive pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional BC association cancels exactly across the two strata, the positive pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (0<selection_BC_pooled_association m<->0<selection_BC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_within_pooled_positive_iff_between_positive :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (0<selection_BC_pooled_association m<->0<selection_BC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_within_pooled_negative_iff_between_negative] (theorem) — If conditional BC association cancels exactly across the two strata, the negative pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional BC association cancels exactly across the two strata, the negative pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (selection_BC_pooled_association m<0<->selection_BC_between_association m<0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_within_pooled_negative_iff_between_negative :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (selection_BC_pooled_association m<0<->selection_BC_between_association m<0).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_within_pooled_zero_iff_between_zero] (theorem) — If conditional BC association cancels exactly across the two strata, the zero pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional BC association cancels exactly across the two strata, the zero pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (selection_BC_pooled_association m=0<->selection_BC_between_association m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_within_pooled_zero_iff_between_zero :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (selection_BC_pooled_association m=0<->selection_BC_between_association m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_within_pooled_nonnegative_iff_between_nonnegative] (theorem) — If conditional BC association cancels exactly across the two strata, the nonnegative pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional BC association cancels exactly across the two strata, the nonnegative pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (0<=selection_BC_pooled_association m<->0<=selection_BC_between_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_within_pooled_nonnegative_iff_between_nonnegative :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (0<=selection_BC_pooled_association m<->0<=selection_BC_between_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_within_pooled_nonpositive_iff_between_nonpositive] (theorem) — If conditional BC association cancels exactly across the two strata, the nonpositive pooled association is determined by selection-induced dependence alone.
 Mathematical meaning: If conditional BC association cancels exactly across the two strata, the nonpositive pooled association is determined by selection-induced dependence alone.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (selection_BC_pooled_association m<=0<->selection_BC_between_association m<=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_within_pooled_nonpositive_iff_between_nonpositive :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_within_association m=0 -> (selection_BC_pooled_association m<=0<->selection_BC_between_association m<=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hw; rewrite Hw in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_between_pooled_positive_iff_within_positive] (theorem) — When selection does not induce between-stratum BC association, positive pooled dependence is exactly positive weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum BC association, positive pooled dependence is exactly positive weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (0<selection_BC_pooled_association m<->0<selection_BC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_between_pooled_positive_iff_within_positive :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (0<selection_BC_pooled_association m<->0<selection_BC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_between_pooled_negative_iff_within_negative] (theorem) — When selection does not induce between-stratum BC association, negative pooled dependence is exactly negative weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum BC association, negative pooled dependence is exactly negative weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (selection_BC_pooled_association m<0<->selection_BC_within_association m<0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_between_pooled_negative_iff_within_negative :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (selection_BC_pooled_association m<0<->selection_BC_within_association m<0).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_between_pooled_zero_iff_within_zero] (theorem) — When selection does not induce between-stratum BC association, zero pooled dependence is exactly zero weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum BC association, zero pooled dependence is exactly zero weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (selection_BC_pooled_association m=0<->selection_BC_within_association m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_between_pooled_zero_iff_within_zero :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (selection_BC_pooled_association m=0<->selection_BC_within_association m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_between_pooled_nonnegative_iff_within_nonnegative] (theorem) — When selection does not induce between-stratum BC association, nonnegative pooled dependence is exactly nonnegative weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum BC association, nonnegative pooled dependence is exactly nonnegative weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (0<=selection_BC_pooled_association m<->0<=selection_BC_within_association m).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_between_pooled_nonnegative_iff_within_nonnegative :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (0<=selection_BC_pooled_association m<->0<=selection_BC_within_association m).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_zero_between_pooled_nonpositive_iff_within_nonpositive] (theorem) — When selection does not induce between-stratum BC association, nonpositive pooled dependence is exactly nonpositive weighted within-stratum dependence.
 Mathematical meaning: When selection does not induce between-stratum BC association, nonpositive pooled dependence is exactly nonpositive weighted within-stratum dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (selection_BC_pooled_association m<=0<->selection_BC_within_association m<=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_zero_between_pooled_nonpositive_iff_within_nonpositive :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_between_association m=0 -> (selection_BC_pooled_association m<=0<->selection_BC_within_association m<=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intro Hb; rewrite Hb in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_BC_within_raw_contingency_cells] (theorem) — The unnormalized BC within-stratum association is an exact positive-mass weighted sum of selected and nonselected four-cell determinants.
 Mathematical meaning: The unnormalized BC within-stratum association is an exact positive-mass weighted sum of selected and nonselected four-cell determinants.
 Exact checked proposition: forall m:ThreeTestModel,  selection_BC_within_association m=selection_BC_other_mass m*reversal_BC_selected_raw_association m+selection_BC_selected_mass m*reversal_BC_other_raw_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_within_raw_contingency_cells :
  forall m:ThreeTestModel,  selection_BC_within_association m=selection_BC_other_mass m*reversal_BC_selected_raw_association m+selection_BC_selected_mass m*reversal_BC_other_raw_association m.
Proof.
  intro m.
  unfold selection_BC_within_association, selection_BC_selected_mass, selection_BC_other_mass, reversal_BC_selected_raw_association, reversal_BC_other_raw_association.
  apply mix_within_explicit.
Qed.

(**
 [reversal_BC_both_strata_independent_within_zero] (theorem) — Conditional independence of BC in both positive- and negative-A subpopulations makes the within association vanish.
 Mathematical meaning: Conditional independence of BC in both positive- and negative-A subpopulations makes the within association vanish.
 Exact checked proposition: forall m:ThreeTestModel,  reversal_BC_selected_raw_association m=0 -> reversal_BC_other_raw_association m=0 -> selection_BC_within_association m=0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_both_strata_independent_within_zero :
  forall m:ThreeTestModel,  reversal_BC_selected_raw_association m=0 -> reversal_BC_other_raw_association m=0 -> selection_BC_within_association m=0.
Proof.
  intros m Hy Hn.
  rewrite reversal_BC_within_raw_contingency_cells.
  rewrite Hy,Hn; ring.
Qed.

(**
 [reversal_BC_conditional_independence_pooled_iff_selection_gap_zero] (theorem) — Under BC independence in both A strata, the population tests are independent precisely when either admission route has no selection-marginal gap.
 Mathematical meaning: Under BC independence in both A strata, the population tests are independent precisely when either admission route has no selection-marginal gap.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m=0 -> reversal_BC_other_raw_association m=0 -> (selection_BC_pooled_association m=0 <-> selection_BC_first_gap m=0 \/ selection_BC_second_gap m=0).
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_conditional_independence_pooled_iff_selection_gap_zero :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m=0 -> reversal_BC_other_raw_association m=0 -> (selection_BC_pooled_association m=0 <-> selection_BC_first_gap m=0 \/ selection_BC_second_gap m=0).
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn.
  pose proof (reversal_BC_both_strata_independent_within_zero m Hy Hn) as Hw.
  pose proof (selection_BC_between_selection_gap_product m) as Hg.
  rewrite Hw, Hg in Hmix.
  split.
  - intro Hp.
    assert (Hzero:selection_BC_first_gap m*selection_BC_second_gap m=0) by nra.
    apply Rmult_integral in Hzero; exact Hzero.
  - intros [Ha|Hb]; rewrite Ha in Hmix || rewrite Hb in Hmix; nra.
Qed.

(**
 [reversal_BC_both_local_negative_within_negative] (theorem) — Strictly negative conditional BC association in both A pass/fail groups produces strictly negative weighted within-stratum association.
 Mathematical meaning: Strictly negative conditional BC association in both A pass/fail groups produces strictly negative weighted within-stratum association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m<0 -> reversal_BC_other_raw_association m<0 -> selection_BC_within_association m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_both_local_negative_within_negative :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m<0 -> reversal_BC_other_raw_association m<0 -> selection_BC_within_association m<0.
Proof.
  intros m Hu Hv Hy Hn.
  rewrite reversal_BC_within_raw_contingency_cells.
  nra.
Qed.

(**
 [reversal_BC_both_local_positive_within_positive] (theorem) — Strictly positive conditional BC association in both A pass/fail groups produces strictly positive weighted within-stratum association.
 Mathematical meaning: Strictly positive conditional BC association in both A pass/fail groups produces strictly positive weighted within-stratum association.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> 0<reversal_BC_selected_raw_association m -> 0<reversal_BC_other_raw_association m -> 0<selection_BC_within_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_both_local_positive_within_positive :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> 0<reversal_BC_selected_raw_association m -> 0<reversal_BC_other_raw_association m -> 0<selection_BC_within_association m.
Proof.
  intros m Hu Hv Hy Hn.
  rewrite reversal_BC_within_raw_contingency_cells.
  nra.
Qed.

(**
 [reversal_BC_positive_simpson_reversal_needs_positive_between] (theorem) — Positive pooled BC association despite negative association within both A strata necessarily requires positive between-stratum selection dependence.
 Mathematical meaning: Positive pooled BC association despite negative association within both A strata necessarily requires positive between-stratum selection dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m<0 -> reversal_BC_other_raw_association m<0 -> 0<selection_BC_pooled_association m -> 0<selection_BC_between_association m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_positive_simpson_reversal_needs_positive_between :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m<0 -> reversal_BC_other_raw_association m<0 -> 0<selection_BC_pooled_association m -> 0<selection_BC_between_association m.
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn Hp.
  pose proof (reversal_BC_both_local_negative_within_negative m Hu Hv Hy Hn) as Hw.
  nra.
Qed.

(**
 [reversal_BC_negative_simpson_reversal_needs_negative_between] (theorem) — Negative pooled BC association despite positive association within both A strata necessarily requires negative between-stratum selection dependence.
 Mathematical meaning: Negative pooled BC association despite positive association within both A strata necessarily requires negative between-stratum selection dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> 0<reversal_BC_selected_raw_association m -> 0<reversal_BC_other_raw_association m -> selection_BC_pooled_association m<0 -> selection_BC_between_association m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_negative_simpson_reversal_needs_negative_between :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> 0<reversal_BC_selected_raw_association m -> 0<reversal_BC_other_raw_association m -> selection_BC_pooled_association m<0 -> selection_BC_between_association m<0.
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hy Hn Hp.
  pose proof (reversal_BC_both_local_positive_within_positive m Hu Hv Hy Hn) as Hw.
  nra.
Qed.

(**
 [reversal_BC_positive_reversal_needs_aligned_selection_gaps] (theorem) — Positive BC Simpson reversal from two negatively associated A strata requires a positive product of the route-specific selected-versus-nonselected pass-rate gaps.
 Mathematical meaning: Positive BC Simpson reversal from two negatively associated A strata requires a positive product of the route-specific selected-versus-nonselected pass-rate gaps.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m<0 -> reversal_BC_other_raw_association m<0 -> 0<selection_BC_pooled_association m -> 0<selection_BC_first_gap m*selection_BC_second_gap m.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_positive_reversal_needs_aligned_selection_gaps :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> reversal_BC_selected_raw_association m<0 -> reversal_BC_other_raw_association m<0 -> 0<selection_BC_pooled_association m -> 0<selection_BC_first_gap m*selection_BC_second_gap m.
Proof.
  intros m Hu Hv Hy Hn Hp.
  pose proof (reversal_BC_positive_simpson_reversal_needs_positive_between m Hu Hv Hy Hn Hp) as Hb.
  rewrite (selection_BC_between_selection_gap_product m) in Hb.
  exact Hb.
Qed.

(**
 [reversal_BC_negative_reversal_needs_opposing_selection_gaps] (theorem) — Negative BC Simpson reversal from two positively associated A strata requires opposite-signed marginal-selection gaps, giving a negative gap product.
 Mathematical meaning: Negative BC Simpson reversal from two positively associated A strata requires opposite-signed marginal-selection gaps, giving a negative gap product.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> 0<reversal_BC_selected_raw_association m -> 0<reversal_BC_other_raw_association m -> selection_BC_pooled_association m<0 -> selection_BC_first_gap m*selection_BC_second_gap m<0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_negative_reversal_needs_opposing_selection_gaps :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> 0<reversal_BC_selected_raw_association m -> 0<reversal_BC_other_raw_association m -> selection_BC_pooled_association m<0 -> selection_BC_first_gap m*selection_BC_second_gap m<0.
Proof.
  intros m Hu Hv Hy Hn Hp.
  pose proof (reversal_BC_negative_simpson_reversal_needs_negative_between m Hu Hv Hy Hn Hp) as Hb.
  rewrite (selection_BC_between_selection_gap_product m) in Hb.
  exact Hb.
Qed.

(**
 [reversal_BC_equal_first_selection_gap_preserves_nonpositive_within] (theorem) — When the BC first-route admission rate does not vary between A groups, nonpositive within-stratum dependence guarantees nonpositive pooled dependence.
 Mathematical meaning: When the BC first-route admission rate does not vary between A groups, nonpositive within-stratum dependence guarantees nonpositive pooled dependence.
 Exact checked proposition: forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_first_gap m=0 -> selection_BC_within_association m<=0 -> selection_BC_pooled_association m<=0.
 Premises and side conditions: The three-test event model supplies eight
 nonnegative masses with unit total. All conditional-selected versus
 nonselected assertions explicitly require positive masses of both strata.
 Conditional independence, signs of local covariances, and equality of
 selection gaps are hypotheses rather than implicit statistical assumptions.
 Proof/definition method: Reuse the previous checked exact pooled-within-between selection factorization, the two-stratum reversal threshold library, and canonical real ring/positivity reasoning; no new distribution-level axioms.
 Library reuse: TwoStratumAssociation, TwoStratumReversal, Admissions and
 ThreeTestSelectionDecomposition, which use the shared FiniteSum/FiniteUnion
 event-mass engines, plus Rocq Stdlib.Reals and Psatz tactics.
 Boundary: Exact finite Boolean event and selection algebra only;
 no multivariate Gaussian tail proof, real admissions estimate, or
 empirical psychometric model follows from this theorem.
*)
Theorem reversal_BC_equal_first_selection_gap_preserves_nonpositive_within :
  forall m:ThreeTestModel, 0<selection_BC_selected_mass m->0<selection_BC_other_mass m-> selection_BC_first_gap m=0 -> selection_BC_within_association m<=0 -> selection_BC_pooled_association m<=0.
Proof.
  intros m Hu Hv.
  pose proof (selection_BC_unit_mass_decomposition m) as Hmix.
  assert (Hpos:0<selection_BC_selected_mass m*selection_BC_other_mass m) by (apply Rmult_lt_0_compat; assumption).
  intros Hg Hw.
  pose proof (selection_BC_between_selection_gap_product m) as Hfactor.
  rewrite Hg in Hfactor.
  assert (Hbetween:selection_BC_between_association m=0) by nra.
  rewrite Hbetween in Hmix; nra.
Qed.

