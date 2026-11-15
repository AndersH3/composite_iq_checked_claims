(** Module: TwoStratumReversal.v
 Purpose: Prove sharp necessary-and-sufficient selection-bias thresholds
 for association reversal, conditional-marginal equality conditions and
 Simpson-style paradox criteria for binary admission indicators.
 Mathematical representation: Reuses the complete, exact eight-real-cell
 two-stratum 2x2 contingency determinant algebra, including the adjusted
 within-plus-between factorization in TwoStratumAssociation.v.
 Explicit hypotheses: Positive masses of both strata are required for
 conditional-rate and equivalence results; local conditional independence
 or within-stratum sign conditions are explicit premises where needed.
 Library use: TwoStratumAssociation, Rocq Stdlib.Reals, Lra, Psatz and Ring;
 existing canonical real inverse and integral-domain library lemmas.
 Limitations: Finite real contingency tables and their exact selection
 threshold algebra; no assertion about Gaussian conditional laws,
 trivariate normal integrals, measured IQ correlations or actual admissions.
 Reproduction: scripts/compile_rocq.sh with pinned Rocq Prover 9.2,
 after the shared TwoStratumAssociation.v source is compiled.
 AI disclosure: OpenAI ChatGPT assisted in writing statements, comments,
 proofs and refactoring. Mathematical validity requires kernel checking.
*)
From Stdlib Require Import Reals Lra Psatz.
Require Import TwoStratumAssociation.
Open Scope R_scope.

(**
 [reversal_pooled_positive_iff_between_threshold] (theorem) — The exact positive pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Mathematical meaning: The exact positive pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) < mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_positive_iff_between_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) < mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_negative_iff_between_threshold] (theorem) — The exact negative pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Mathematical meaning: The exact negative pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 < - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_negative_iff_between_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 < - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_zero_iff_between_threshold] (theorem) — The exact zero pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Mathematical meaning: The exact zero pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 = - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_zero_iff_between_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 = - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_nonnegative_iff_between_threshold] (theorem) — The exact nonnegative pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Mathematical meaning: The exact nonnegative pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) <= mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_nonnegative_iff_between_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) <= mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_nonpositive_iff_between_threshold] (theorem) — The exact nonpositive pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Mathematical meaning: The exact nonpositive pooled association criterion is a sharp comparison of selection-induced association with the negative weighted within-stratum association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 <= - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_nonpositive_iff_between_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 <= - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_positive_iff_within_threshold] (theorem) — The exact positive pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Mathematical meaning: The exact positive pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - mix_between j1 x1 y1 n1 j0 x0 y0 n0 < ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_positive_iff_within_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - mix_between j1 x1 y1 n1 j0 x0 y0 n0 < ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_negative_iff_within_threshold] (theorem) — The exact negative pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Mathematical meaning: The exact negative pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) < - mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_negative_iff_within_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) < - mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_zero_iff_within_threshold] (theorem) — The exact zero pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Mathematical meaning: The exact zero pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) = - mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_zero_iff_within_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) = - mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_nonnegative_iff_within_threshold] (theorem) — The exact nonnegative pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Mathematical meaning: The exact nonnegative pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - mix_between j1 x1 y1 n1 j0 x0 y0 n0 <= ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_nonnegative_iff_within_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - mix_between j1 x1 y1 n1 j0 x0 y0 n0 <= ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_pooled_nonpositive_iff_within_threshold] (theorem) — The exact nonpositive pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Mathematical meaning: The exact nonpositive pooled association condition is equivalent to the corrected within-association crossing its negative between-selection threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) <= - mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_pooled_nonpositive_iff_within_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) <= - mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_within_pooled_positive_iff] (theorem) — When zero within vanishes, the pooled association is positive exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero within vanishes, the pooled association is positive exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_within_pooled_positive_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_within_pooled_negative_iff] (theorem) — When zero within vanishes, the pooled association is negative exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero within vanishes, the pooled association is negative exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0<0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_within_pooled_negative_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0<0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_within_pooled_zero_iff] (theorem) — When zero within vanishes, the pooled association is zero exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero within vanishes, the pooled association is zero exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_within_pooled_zero_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_within_pooled_nonnegative_iff] (theorem) — When zero within vanishes, the pooled association is nonnegative exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero within vanishes, the pooled association is nonnegative exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_within_pooled_nonnegative_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<=mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_within_pooled_nonpositive_iff] (theorem) — When zero within vanishes, the pooled association is nonpositive exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero within vanishes, the pooled association is nonpositive exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_within_pooled_nonpositive_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0<=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_between_pooled_positive_iff] (theorem) — When zero between vanishes, the pooled association is positive exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero between vanishes, the pooled association is positive exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_between_pooled_positive_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_between_pooled_negative_iff] (theorem) — When zero between vanishes, the pooled association is negative exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero between vanishes, the pooled association is negative exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)<0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_between_pooled_negative_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)<0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_between_pooled_zero_iff] (theorem) — When zero between vanishes, the pooled association is zero exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero between vanishes, the pooled association is zero exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_between_pooled_zero_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_between_pooled_nonnegative_iff] (theorem) — When zero between vanishes, the pooled association is nonnegative exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero between vanishes, the pooled association is nonnegative exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<=((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_between_pooled_nonnegative_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> 0<=((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_zero_between_pooled_nonpositive_iff] (theorem) — When zero between vanishes, the pooled association is nonpositive exactly when the remaining component has the corresponding sign.
 Mathematical meaning: When zero between vanishes, the pooled association is nonpositive exactly when the remaining component has the corresponding sign.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)<=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_zero_between_pooled_nonpositive_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_between j1 x1 y1 n1 j0 x0 y0 n0=0 -> (mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<=0 <-> ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)<=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intro Hzero; rewrite Hzero in Hmix; split; intro Hsign; nra.
Qed.

(**
 [reversal_equal_first_selection_marginal_preserves_positive] (theorem) — No selected-versus-unselected shift in the first marginal removes the between-stratum association; positive within association then implies positive pooled association.
 Mathematical meaning: No selected-versus-unselected shift in the first marginal removes the between-stratum association; positive within association then implies positive pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 -> 0<mix_within j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_equal_first_selection_marginal_preserves_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 -> 0<mix_within j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros Hgap Hwithin.
  rewrite mix_between_explicit in Hmix.
  rewrite Hgap in Hmix.
  nra.
Qed.

(**
 [reversal_equal_first_selection_marginal_preserves_negative] (theorem) — No selected-versus-unselected shift in the first marginal removes the between-stratum association; negative within association then implies negative pooled association.
 Mathematical meaning: No selected-versus-unselected shift in the first marginal removes the between-stratum association; negative within association then implies negative pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_equal_first_selection_marginal_preserves_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros Hgap Hwithin.
  rewrite mix_between_explicit in Hmix.
  rewrite Hgap in Hmix.
  nra.
Qed.

(**
 [reversal_equal_first_selection_marginal_preserves_zero] (theorem) — No selected-versus-unselected shift in the first marginal removes the between-stratum association; zero within association then implies zero pooled association.
 Mathematical meaning: No selected-versus-unselected shift in the first marginal removes the between-stratum association; zero within association then implies zero pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_equal_first_selection_marginal_preserves_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros Hgap Hwithin.
  rewrite mix_between_explicit in Hmix.
  rewrite Hgap in Hmix.
  nra.
Qed.

(**
 [reversal_equal_second_selection_marginal_preserves_positive] (theorem) — No selected-versus-unselected shift in the second marginal removes the between-stratum association; positive within association then implies positive pooled association.
 Mathematical meaning: No selected-versus-unselected shift in the second marginal removes the between-stratum association; positive within association then implies positive pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0 -> 0<mix_within j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_equal_second_selection_marginal_preserves_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0 -> 0<mix_within j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros Hgap Hwithin.
  rewrite mix_between_explicit in Hmix.
  rewrite Hgap in Hmix.
  nra.
Qed.

(**
 [reversal_equal_second_selection_marginal_preserves_negative] (theorem) — No selected-versus-unselected shift in the second marginal removes the between-stratum association; negative within association then implies negative pooled association.
 Mathematical meaning: No selected-versus-unselected shift in the second marginal removes the between-stratum association; negative within association then implies negative pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_equal_second_selection_marginal_preserves_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros Hgap Hwithin.
  rewrite mix_between_explicit in Hmix.
  rewrite Hgap in Hmix.
  nra.
Qed.

(**
 [reversal_equal_second_selection_marginal_preserves_zero] (theorem) — No selected-versus-unselected shift in the second marginal removes the between-stratum association; zero within association then implies zero pooled association.
 Mathematical meaning: No selected-versus-unselected shift in the second marginal removes the between-stratum association; zero within association then implies zero pooled association.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_equal_second_selection_marginal_preserves_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_within j1 x1 y1 n1 j0 x0 y0 n0=0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros Hgap Hwithin.
  rewrite mix_between_explicit in Hmix.
  rewrite Hgap in Hmix.
  nra.
Qed.

(**
 [reversal_both_strata_independent_within_zero] (theorem) — Conditional independence in each selection stratum makes the total weighted within-stratum association exactly zero.
 Mathematical meaning: Conditional independence in each selection stratum makes the total weighted within-stratum association exactly zero.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0=0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_both_strata_independent_within_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0=0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv H1 H0.
  rewrite mix_within_explicit, H1, H0.
  ring.
Qed.

(**
 [reversal_both_strata_independent_pooled_positive_iff] (theorem) — Under conditional independence in both subpopulations, positive marginal dependence is determined entirely by the two selection-rate gaps.
 Mathematical meaning: Under conditional independence in both subpopulations, positive marginal dependence is determined entirely by the two selection-rate gaps.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_both_strata_independent_pooled_positive_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  rewrite mix_within_explicit, mix_between_explicit in Hmix.
  rewrite H1, H0 in Hmix.
  ring_simplify in Hmix.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_both_strata_independent_pooled_negative_iff] (theorem) — Under conditional independence in both subpopulations, negative marginal dependence is determined entirely by the two selection-rate gaps.
 Mathematical meaning: Under conditional independence in both subpopulations, negative marginal dependence is determined entirely by the two selection-rate gaps.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_both_strata_independent_pooled_negative_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  rewrite mix_within_explicit, mix_between_explicit in Hmix.
  rewrite H1, H0 in Hmix.
  ring_simplify in Hmix.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_both_strata_independent_pooled_zero_iff] (theorem) — Under conditional independence in both subpopulations, zero marginal dependence is determined entirely by the two selection-rate gaps.
 Mathematical meaning: Under conditional independence in both subpopulations, zero marginal dependence is determined entirely by the two selection-rate gaps.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_both_strata_independent_pooled_zero_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  rewrite mix_within_explicit, mix_between_explicit in Hmix.
  rewrite H1, H0 in Hmix.
  ring_simplify in Hmix.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_both_strata_independent_pooled_nonnegative_iff] (theorem) — Under conditional independence in both subpopulations, nonnegative marginal dependence is determined entirely by the two selection-rate gaps.
 Mathematical meaning: Under conditional independence in both subpopulations, nonnegative marginal dependence is determined entirely by the two selection-rate gaps.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_both_strata_independent_pooled_nonnegative_iff :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(0<=mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<->0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0*mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  rewrite mix_within_explicit, mix_between_explicit in Hmix.
  rewrite H1, H0 in Hmix.
  ring_simplify in Hmix.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_both_strata_independent_pooled_independence_iff_gap_zero] (theorem) — When both strata are conditionally independent, the pooled tests remain independent precisely if at least one route has zero selected-versus-other pass-rate gap.
 Mathematical meaning: When both strata are conditionally independent, the pooled tests remain independent precisely if at least one route has zero selected-versus-other pass-rate gap.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 \/ mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_both_strata_independent_pooled_independence_iff_gap_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0=0 <-> mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0 \/ mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  pose proof (reversal_both_strata_independent_pooled_zero_iff j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv H1 H0) as Hiff.
  rewrite Hiff.
  rewrite <- mix_between_explicit.
  rewrite mix_between_explicit.
  split.
  - apply Rmult_integral.
  - intros [Ha|Hb]; rewrite Ha || rewrite Hb; ring.
Qed.

(**
 [reversal_positive_reversal_requires_positive_selection] (theorem) — With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Mathematical meaning: With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0 -> 0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_positive_reversal_requires_positive_selection :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0 -> 0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0->0<mix_between j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0 Hp.
  pose proof (mix_within_negative_from_first_strict j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv H1 (Rlt_le _ _ H0)) as Hw.
  nra.
Qed.

(**
 [reversal_negative_reversal_requires_negative_selection] (theorem) — With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Mathematical meaning: With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_negative_reversal_requires_negative_selection :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0 -> mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0->mix_between j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0 Hp.
  pose proof (mix_within_positive_from_first_strict j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv H1 (Rlt_le _ _ H0)) as Hw.
  nra.
Qed.

(**
 [reversal_positive_reversal_iff_threshold] (theorem) — With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Mathematical meaning: With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0->(0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) < mix_between j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_positive_reversal_iff_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0 -> mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0->(0<mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0 <-> - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0) < mix_between j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  pose proof (reversal_pooled_positive_iff_between_threshold j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hiff.
  exact Hiff.
Qed.

(**
 [reversal_negative_reversal_iff_threshold] (theorem) — With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Mathematical meaning: With the two within-stratum association determinants constrained to the same strict sign, the exact marginal sign-reversal requires the correct signed selection effect and threshold.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 < - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_negative_reversal_iff_threshold :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0 -> 0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->(mix_pooled_association j1 x1 y1 n1 j0 x0 y0 n0<0 <-> mix_between j1 x1 y1 n1 j0 x0 y0 n0 < - ((mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)*mix_within j1 x1 y1 n1 j0 x0 y0 n0)).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  pose proof (reversal_pooled_negative_iff_between_threshold j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hiff.
  exact Hiff.
Qed.

(**
 [reversal_yes_positive_other_independent_within_sign] (theorem) — When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Mathematical meaning: When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_yes_positive_other_independent_within_sign :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> 0<mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  apply (mix_within_positive_from_first_strict j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv); lra.
Qed.

(**
 [reversal_other_positive_yes_independent_within_sign] (theorem) — When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Mathematical meaning: When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_other_positive_yes_independent_within_sign :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->0<mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0->0<mix_within j1 x1 y1 n1 j0 x0 y0 n0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  apply (mix_within_positive_from_second_strict j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv); lra.
Qed.

(**
 [reversal_yes_negative_other_independent_within_sign] (theorem) — When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Mathematical meaning: When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_yes_negative_other_independent_within_sign :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0<0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0=0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  apply (mix_within_negative_from_first_strict j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv); lra.
Qed.

(**
 [reversal_other_negative_yes_independent_within_sign] (theorem) — When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Mathematical meaning: When exactly one stratum has nonzero association and the other is conditionally independent, the sign of the within contribution follows the associated stratum.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_other_negative_yes_independent_within_sign :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> mix_local_assoc_yes j1 x1 y1 n1 j0 x0 y0 n0=0->mix_local_assoc_no j1 x1 y1 n1 j0 x0 y0 n0<0->mix_within j1 x1 y1 n1 j0 x0 y0 n0<0.
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  intros H1 H0.
  apply (mix_within_negative_from_second_strict j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv); lra.
Qed.

(**
 [reversal_first_selection_rate_positive_iff_gap_positive] (theorem) — The positive selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The positive selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_first_selection_rate_positive_iff_gap_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_first_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_first_selection_rate_negative_iff_gap_negative] (theorem) — The negative selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The negative selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_first_selection_rate_negative_iff_gap_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_first_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_first_selection_rate_zero_iff_gap_zero] (theorem) — The zero selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The zero selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)=0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_first_selection_rate_zero_iff_gap_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)=0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_first_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_first_selection_rate_nonnegative_iff_gap_nonnegative] (theorem) — The nonnegative selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The nonnegative selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_first_selection_rate_nonnegative_iff_gap_nonnegative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<=mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_first_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_first_selection_rate_nonpositive_iff_gap_nonpositive] (theorem) — The nonpositive selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The nonpositive selected-versus-unselected conditional first-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<=0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_first_selection_rate_nonpositive_iff_gap_nonpositive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+x1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+x0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<=0<->mix_gap_first j1 x1 y1 n1 j0 x0 y0 n0<=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_first_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_second_selection_rate_positive_iff_gap_positive] (theorem) — The positive selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The positive selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_second_selection_rate_positive_iff_gap_positive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_second_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_second_selection_rate_negative_iff_gap_negative] (theorem) — The negative selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The negative selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<0<->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_second_selection_rate_negative_iff_gap_negative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<0<->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_second_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_second_selection_rate_zero_iff_gap_zero] (theorem) — The zero selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The zero selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)=0<->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_second_selection_rate_zero_iff_gap_zero :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)=0<->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_second_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_second_selection_rate_nonnegative_iff_gap_nonnegative] (theorem) — The nonnegative selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The nonnegative selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_second_selection_rate_nonnegative_iff_gap_nonnegative :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (0<=((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<->0<=mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_second_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

(**
 [reversal_second_selection_rate_nonpositive_iff_gap_nonpositive] (theorem) — The nonpositive selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Mathematical meaning: The nonpositive selected-versus-unselected conditional second-route admission-rate difference has exactly the sign of the cross-multiplied selection gap, with both denominators positive.
 Exact checked proposition: forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<=0<->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<=0).
 Premises and side conditions: All needed conditions are displayed in
 the statement: raw real contingency cells need no sign premises for ring
 identities; pooled-versus-stratified sign equivalences require two strictly
 positive selected and unselected masses, and the corresponding local
 dependence and group selection-gap restrictions are explicitly stated.
 Proof/definition method: Reuse the established TwoStratumAssociation
 exact determinant decomposition and its checked signed within/between
 criteria; apply only trusted Stdlib real-linear and nonlinear arithmetic,
 canonical inverse positivity or the real integral-domain product lemma.
 Library reuse: TwoStratumAssociation.v, Rocq Stdlib.Reals, Lra, Psatz.
 No new probability sums, covariance definitions, or matrix code.
 Boundary: Finite two-stratum binary-event association algebra only;
 no Gaussian conditional laws, normal tail integrals, or empirical IQ data.
*)
Theorem reversal_second_selection_rate_nonpositive_iff_gap_nonpositive :
  forall j1 x1 y1 n1 j0 x0 y0 n0 : R, 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0->0<mix_total_no j1 x1 y1 n1 j0 x0 y0 n0-> (((j1+y1)/mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0-(j0+y0)/mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)<=0<->mix_gap_second j1 x1 y1 n1 j0 x0 y0 n0<=0).
Proof.
  intros j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv.
  pose proof (mix_stratified_association_identity j1 x1 y1 n1 j0 x0 y0 n0) as Hmix.
  assert (Hpositive : 0<mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0) by (apply Rmult_lt_0_compat; assumption).
  assert (Htotal : 0<(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0+mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by lra.
  pose proof (mix_second_rate_gap_exact j1 x1 y1 n1 j0 x0 y0 n0 Hu Hv) as Hrate.
  assert (Hinv : 0 < /(mix_total_yes j1 x1 y1 n1 j0 x0 y0 n0*mix_total_no j1 x1 y1 n1 j0 x0 y0 n0)) by (apply Rinv_0_lt_compat; exact Hpositive).
  unfold Rdiv in Hrate.
  split; intro Hsign; nra.
Qed.

