(** Module: ThreeTestConditionalStrata.v
  Purpose: Prove exact third-test selection/stratification identities and
  conditional dependence results needed to analyze multiple admissions tests,
  including conditional association, odds, Bernoulli phi and Simpson reversal.
  Mathematical representation: The eight Boolean atom weights of the existing
  ThreeTestModel give six four-cell conditional distributions: AB given C,
  AC given B and BC given A, each in positive and negative selection strata.
  Explicit hypotheses: ThreeTestModel supplies nonnegative normalized mass.
  Every normalized conditional two-event model has an explicit positive
  stratum-probability proof; conditionals/odds/phi require additional positive
  denominators wherever they have a probabilistic interpretation.
  Library use: Admissions.TwoEventModel with already-proved conditional,
  Fréchet, covariance, independence, odds and phi theorems, the
  ThreeTestAdmissions model and its canonical FiniteUnion/FiniteSum engine;
  trusted Stdlib.Reals, Lra, Psatz and Field. No new finite-sum recursion.
  Limitations: This proves exact finite Boolean-event selection algebra,
  not Gaussian conditioning, normal tail probabilities, or real-world IQ
  and admission calibration.
  Reproduction: scripts/compile_rocq.sh pinned to Rocq Prover 9.2,
  after Admissions and ThreeTestAdmissions in the ordered build.
  AI disclosure: Formal statements, source commentary and proof scripts
  were AI-assisted; only a successful Rocq kernel check establishes proofs.
*)
From Stdlib Require Import Reals Lra Psatz.
Require Import Admissions ThreeTestAdmissions.
Open Scope R_scope.

(** [normalized_four_stratum] builds one certified two-test distribution
 from four nonnegative unnormalized joint/exclusive/neither masses.
 Mathematical meaning: Dividing all four cells by their strictly positive
 total creates a FourCellModel with exact unit probability mass.
 Exact declaration: Positive homogeneous normalization of four real masses.
 Premises and side conditions: All four raw masses must be nonnegative,
 and their sum must be strictly positive; independence is not assumed.
 Proof/definition method: Standard real division by positive total and
 Admissions.TwoEventModel record obligations discharged via Rocq field
 and nonnegative-inverse lemmas; no custom probability summation.
 Library reuse: Admissions.TwoEventModel, Stdlib.Reals and Field.
 Boundary: A normalized finite contingency table, not a Gaussian law.
*)
Definition normalized_four_stratum
 (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n)
 (Ht:0<j+x+y+n) : Admissions.TwoEventModel.
Proof.
  refine {| Admissions.joint := j/(j+x+y+n);
            Admissions.only_A := x/(j+x+y+n);
            Admissions.only_B := y/(j+x+y+n);
            Admissions.neither := n/(j+x+y+n) |}.
  - unfold Rdiv; apply Rmult_le_pos.
    + exact Hj.
    + apply Rlt_le, Rinv_0_lt_compat; exact Ht.
  - unfold Rdiv; apply Rmult_le_pos.
    + exact Hx.
    + apply Rlt_le, Rinv_0_lt_compat; exact Ht.
  - unfold Rdiv; apply Rmult_le_pos.
    + exact Hy.
    + apply Rlt_le, Rinv_0_lt_compat; exact Ht.
  - unfold Rdiv; apply Rmult_le_pos.
    + exact Hn.
    + apply Rlt_le, Rinv_0_lt_compat; exact Ht.
  - field; lra.
Defined.

(**
 [stratum_ab_c_yes] (definition) — Conditioning pair AB on the pass stratum of test C yields a normalized, nonnegative two-test contingency table.
 Mathematical meaning: Conditioning pair AB on the pass stratum of test C yields a normalized, nonnegative two-test contingency table.
 Exact declaration: forall (m:ThreeTestModel) (H:0<pC3 m), Admissions.TwoEventModel
 Premises and side conditions: The raw three-test model has eight
 nonnegative atoms summing to one. The explicit stratum condition is strictly positive and certifies that normalization is defined.
 Proof/definition method: Use the single normalized_four_stratum constructor with four raw masses; prove its positive total by canonical eight-cell normalization.
 Library reuse: Admissions.TwoEventModel and checked probability/association
 theorems; ThreeTestAdmissions.triple_lra; FiniteUnion.finite_prob,
 FiniteSum.finite_sum; Stdlib.Reals, Lra and Field. No new summation engine.
 Boundary: Finite conditional Boolean-event calculations, not Gaussian
 conditional regression, normal tail integrals, or empirical IQ claims.
*)
Definition stratum_ab_c_yes (m:ThreeTestModel) (H:0<pC3 m) : Admissions.TwoEventModel.
Proof.
  refine (normalized_four_stratum
    (mass3 m (true,true,true)) (mass3 m (true,false,true)) (mass3 m (false,true,true)) (mass3 m (false,false,true))
    (mass3_nonnegative m (true,true,true))
    (mass3_nonnegative m (true,false,true))
    (mass3_nonnegative m (false,true,true))
    (mass3_nonnegative m (false,false,true)) _).
  pose proof H as Hpositive.
  triple_lra.
Defined.

(**
 [stratum_ab_c_no] (definition) — Conditioning pair AB on the failure stratum of test C yields a normalized, nonnegative two-test contingency table.
 Mathematical meaning: Conditioning pair AB on the failure stratum of test C yields a normalized, nonnegative two-test contingency table.
 Exact declaration: forall (m:ThreeTestModel) (H:0<1-pC3 m), Admissions.TwoEventModel
 Premises and side conditions: The raw three-test model has eight
 nonnegative atoms summing to one. The explicit stratum condition is strictly positive and certifies that normalization is defined.
 Proof/definition method: Use the single normalized_four_stratum constructor with four raw masses; prove its positive total by canonical eight-cell normalization.
 Library reuse: Admissions.TwoEventModel and checked probability/association
 theorems; ThreeTestAdmissions.triple_lra; FiniteUnion.finite_prob,
 FiniteSum.finite_sum; Stdlib.Reals, Lra and Field. No new summation engine.
 Boundary: Finite conditional Boolean-event calculations, not Gaussian
 conditional regression, normal tail integrals, or empirical IQ claims.
*)
Definition stratum_ab_c_no (m:ThreeTestModel) (H:0<1-pC3 m) : Admissions.TwoEventModel.
Proof.
  refine (normalized_four_stratum
    (mass3 m (true,true,false)) (mass3 m (true,false,false)) (mass3 m (false,true,false)) (mass3 m (false,false,false))
    (mass3_nonnegative m (true,true,false))
    (mass3_nonnegative m (true,false,false))
    (mass3_nonnegative m (false,true,false))
    (mass3_nonnegative m (false,false,false)) _).
  pose proof H as Hpositive.
  triple_lra.
Defined.

(**
 [stratum_ac_b_yes] (definition) — Conditioning pair AC on the pass stratum of test B yields a normalized, nonnegative two-test contingency table.
 Mathematical meaning: Conditioning pair AC on the pass stratum of test B yields a normalized, nonnegative two-test contingency table.
 Exact declaration: forall (m:ThreeTestModel) (H:0<pB3 m), Admissions.TwoEventModel
 Premises and side conditions: The raw three-test model has eight
 nonnegative atoms summing to one. The explicit stratum condition is strictly positive and certifies that normalization is defined.
 Proof/definition method: Use the single normalized_four_stratum constructor with four raw masses; prove its positive total by canonical eight-cell normalization.
 Library reuse: Admissions.TwoEventModel and checked probability/association
 theorems; ThreeTestAdmissions.triple_lra; FiniteUnion.finite_prob,
 FiniteSum.finite_sum; Stdlib.Reals, Lra and Field. No new summation engine.
 Boundary: Finite conditional Boolean-event calculations, not Gaussian
 conditional regression, normal tail integrals, or empirical IQ claims.
*)
Definition stratum_ac_b_yes (m:ThreeTestModel) (H:0<pB3 m) : Admissions.TwoEventModel.
Proof.
  refine (normalized_four_stratum
    (mass3 m (true,true,true)) (mass3 m (true,true,false)) (mass3 m (false,true,true)) (mass3 m (false,true,false))
    (mass3_nonnegative m (true,true,true))
    (mass3_nonnegative m (true,true,false))
    (mass3_nonnegative m (false,true,true))
    (mass3_nonnegative m (false,true,false)) _).
  pose proof H as Hpositive.
  triple_lra.
Defined.

(**
 [stratum_ac_b_no] (definition) — Conditioning pair AC on the failure stratum of test B yields a normalized, nonnegative two-test contingency table.
 Mathematical meaning: Conditioning pair AC on the failure stratum of test B yields a normalized, nonnegative two-test contingency table.
 Exact declaration: forall (m:ThreeTestModel) (H:0<1-pB3 m), Admissions.TwoEventModel
 Premises and side conditions: The raw three-test model has eight
 nonnegative atoms summing to one. The explicit stratum condition is strictly positive and certifies that normalization is defined.
 Proof/definition method: Use the single normalized_four_stratum constructor with four raw masses; prove its positive total by canonical eight-cell normalization.
 Library reuse: Admissions.TwoEventModel and checked probability/association
 theorems; ThreeTestAdmissions.triple_lra; FiniteUnion.finite_prob,
 FiniteSum.finite_sum; Stdlib.Reals, Lra and Field. No new summation engine.
 Boundary: Finite conditional Boolean-event calculations, not Gaussian
 conditional regression, normal tail integrals, or empirical IQ claims.
*)
Definition stratum_ac_b_no (m:ThreeTestModel) (H:0<1-pB3 m) : Admissions.TwoEventModel.
Proof.
  refine (normalized_four_stratum
    (mass3 m (true,false,true)) (mass3 m (true,false,false)) (mass3 m (false,false,true)) (mass3 m (false,false,false))
    (mass3_nonnegative m (true,false,true))
    (mass3_nonnegative m (true,false,false))
    (mass3_nonnegative m (false,false,true))
    (mass3_nonnegative m (false,false,false)) _).
  pose proof H as Hpositive.
  triple_lra.
Defined.

(**
 [stratum_bc_a_yes] (definition) — Conditioning pair BC on the pass stratum of test A yields a normalized, nonnegative two-test contingency table.
 Mathematical meaning: Conditioning pair BC on the pass stratum of test A yields a normalized, nonnegative two-test contingency table.
 Exact declaration: forall (m:ThreeTestModel) (H:0<pA3 m), Admissions.TwoEventModel
 Premises and side conditions: The raw three-test model has eight
 nonnegative atoms summing to one. The explicit stratum condition is strictly positive and certifies that normalization is defined.
 Proof/definition method: Use the single normalized_four_stratum constructor with four raw masses; prove its positive total by canonical eight-cell normalization.
 Library reuse: Admissions.TwoEventModel and checked probability/association
 theorems; ThreeTestAdmissions.triple_lra; FiniteUnion.finite_prob,
 FiniteSum.finite_sum; Stdlib.Reals, Lra and Field. No new summation engine.
 Boundary: Finite conditional Boolean-event calculations, not Gaussian
 conditional regression, normal tail integrals, or empirical IQ claims.
*)
Definition stratum_bc_a_yes (m:ThreeTestModel) (H:0<pA3 m) : Admissions.TwoEventModel.
Proof.
  refine (normalized_four_stratum
    (mass3 m (true,true,true)) (mass3 m (true,true,false)) (mass3 m (true,false,true)) (mass3 m (true,false,false))
    (mass3_nonnegative m (true,true,true))
    (mass3_nonnegative m (true,true,false))
    (mass3_nonnegative m (true,false,true))
    (mass3_nonnegative m (true,false,false)) _).
  pose proof H as Hpositive.
  triple_lra.
Defined.

(**
 [stratum_bc_a_no] (definition) — Conditioning pair BC on the failure stratum of test A yields a normalized, nonnegative two-test contingency table.
 Mathematical meaning: Conditioning pair BC on the failure stratum of test A yields a normalized, nonnegative two-test contingency table.
 Exact declaration: forall (m:ThreeTestModel) (H:0<1-pA3 m), Admissions.TwoEventModel
 Premises and side conditions: The raw three-test model has eight
 nonnegative atoms summing to one. The explicit stratum condition is strictly positive and certifies that normalization is defined.
 Proof/definition method: Use the single normalized_four_stratum constructor with four raw masses; prove its positive total by canonical eight-cell normalization.
 Library reuse: Admissions.TwoEventModel and checked probability/association
 theorems; ThreeTestAdmissions.triple_lra; FiniteUnion.finite_prob,
 FiniteSum.finite_sum; Stdlib.Reals, Lra and Field. No new summation engine.
 Boundary: Finite conditional Boolean-event calculations, not Gaussian
 conditional regression, normal tail integrals, or empirical IQ claims.
*)
Definition stratum_bc_a_no (m:ThreeTestModel) (H:0<1-pA3 m) : Admissions.TwoEventModel.
Proof.
  refine (normalized_four_stratum
    (mass3 m (false,true,true)) (mass3 m (false,true,false)) (mass3 m (false,false,true)) (mass3 m (false,false,false))
    (mass3_nonnegative m (false,true,true))
    (mass3_nonnegative m (false,true,false))
    (mass3_nonnegative m (false,false,true))
    (mass3_nonnegative m (false,false,false)) _).
  pose proof H as Hpositive.
  triple_lra.
Defined.

(**
 [normalized_four_joint_scaled] (theorem) — Scaling the joint conditional-admission probability by the positive stratum total recovers the original joint mass.
 Mathematical meaning: Scaling the joint conditional-admission probability by the positive stratum total recovers the original joint mass.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.p_both (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_joint_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.p_both (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  unfold Admissions.p_both; simpl; field; lra.
Qed.

(**
 [normalized_four_only_first_scaled] (theorem) — The conditional first-only cell rescales to the corresponding unnormalized exclusive mass.
 Mathematical meaning: The conditional first-only cell rescales to the corresponding unnormalized exclusive mass.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.only_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=x.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_only_first_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.only_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=x.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  simpl; field; lra.
Qed.

(**
 [normalized_four_only_second_scaled] (theorem) — The conditional second-only cell rescales to the corresponding unnormalized exclusive mass.
 Mathematical meaning: The conditional second-only cell rescales to the corresponding unnormalized exclusive mass.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.only_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=y.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_only_second_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.only_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=y.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  simpl; field; lra.
Qed.

(**
 [normalized_four_neither_scaled] (theorem) — The conditional neither-cell rescales to the corresponding raw neither mass.
 Mathematical meaning: The conditional neither-cell rescales to the corresponding raw neither mass.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.neither (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=n.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_neither_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.neither (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=n.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  simpl; field; lra.
Qed.

(**
 [normalized_four_first_scaled] (theorem) — Multiplying the first conditional admission marginal by the selection mass yields its joint plus exclusive raw masses.
 Mathematical meaning: Multiplying the first conditional admission marginal by the selection mass yields its joint plus exclusive raw masses.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.p_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j+x.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_first_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.p_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j+x.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  unfold Admissions.p_A; simpl; field; lra.
Qed.

(**
 [normalized_four_second_scaled] (theorem) — Multiplying the second conditional admission marginal by the selection mass yields its joint plus exclusive raw masses.
 Mathematical meaning: Multiplying the second conditional admission marginal by the selection mass yields its joint plus exclusive raw masses.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.p_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j+y.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_second_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.p_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j+y.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  unfold Admissions.p_B; simpl; field; lra.
Qed.

(**
 [normalized_four_union_scaled] (theorem) — Conditional union mass equals the joint-plus-two-exclusive raw masses divided by the stratum total.
 Mathematical meaning: Conditional union mass equals the joint-plus-two-exclusive raw masses divided by the stratum total.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.p_either (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j+x+y.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_union_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.p_either (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j+x+y.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  unfold Admissions.p_either; simpl; field; lra.
Qed.

(**
 [normalized_four_exclusive_scaled] (theorem) — The two-route exactly-one conditional admission probability rescales to the sum of two exclusive masses.
 Mathematical meaning: The two-route exactly-one conditional admission probability rescales to the sum of two exclusive masses.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*Admissions.p_exactly_one (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=x+y.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_exclusive_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*Admissions.p_exactly_one (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=x+y.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  unfold Admissions.p_exactly_one; simpl; field; lra.
Qed.

(**
 [normalized_four_association_scaled] (theorem) — Selection probability squared times conditional association equals the unnormalized two-by-two determinant of raw strata cells.
 Mathematical meaning: Selection probability squared times conditional association equals the unnormalized two-by-two determinant of raw strata cells.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (j+x+y+n)*(j+x+y+n)*Admissions.admission_association (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j*n-x*y.
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_association_scaled :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (j+x+y+n)*(j+x+y+n)*Admissions.admission_association (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j*n-x*y.
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  unfold Admissions.admission_association; simpl; field; lra.
Qed.

(**
 [normalized_four_independent_iff] (theorem) — Conditional independence in a normalized stratum is equivalent to the exact zero determinant of its four raw cells.
 Mathematical meaning: Conditional independence in a normalized stratum is equivalent to the exact zero determinant of its four raw cells.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (Admissions.p_both (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=Admissions.p_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)*Admissions.p_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht) <-> j*n=x*y).
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_independent_iff :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (Admissions.p_both (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=Admissions.p_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)*Admissions.p_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht) <-> j*n=x*y).
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  rewrite <- (Admissions.admission_association_zero_iff_independence (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)).
  pose proof (normalized_four_association_scaled j x y n Hj Hx Hy Hn Ht) as Hscaled.
  assert (Hpositive:0<(j+x+y+n)*(j+x+y+n)) by nra.
  split; intro H.
  - rewrite H in Hscaled; lra.
  - assert (Hzero:(j+x+y+n)*(j+x+y+n)*Admissions.admission_association (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=0) by lra.
    apply Rmult_integral in Hzero.
    destruct Hzero as [Htzero | Hassoc]; [exfalso; nra|exact Hassoc].
Qed.

(**
 [normalized_four_positive_association_iff] (theorem) — Positive conditional association is equivalent to concordant raw cell product exceeding discordant product.
 Mathematical meaning: Positive conditional association is equivalent to concordant raw cell product exceeding discordant product.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (0<Admissions.admission_association (normalized_four_stratum j x y n Hj Hx Hy Hn Ht) <-> x*y<j*n).
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_positive_association_iff :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (0<Admissions.admission_association (normalized_four_stratum j x y n Hj Hx Hy Hn Ht) <-> x*y<j*n).
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  pose proof (normalized_four_association_scaled j x y n Hj Hx Hy Hn Ht) as Hscaled.
  assert (Hpositive:0<(j+x+y+n)*(j+x+y+n)) by nra.
  split; intro H; nra.
Qed.

(**
 [normalized_four_negative_association_iff] (theorem) — Negative conditional association is equivalent to the concordant raw cell product lying below discordant product.
 Mathematical meaning: Negative conditional association is equivalent to the concordant raw cell product lying below discordant product.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), (Admissions.admission_association (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)<0 <-> j*n<x*y).
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_negative_association_iff :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  (Admissions.admission_association (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)<0 <-> j*n<x*y).
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  pose proof (normalized_four_association_scaled j x y n Hj Hx Hy Hn Ht) as Hscaled.
  assert (Hpositive:0<(j+x+y+n)*(j+x+y+n)) by nra.
  split; intro H; nra.
Qed.

(**
 [normalized_four_odds_ratio_raw] (theorem) — Conditioning on a nonempty stratum preserves the odds ratio of its four unnormalized cells, provided both discordant masses are positive.
 Mathematical meaning: Conditioning on a nonempty stratum preserves the odds ratio of its four unnormalized cells, provided both discordant masses are positive.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), 0<x*y -> Admissions.admission_odds_ratio (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j*n/(x*y).
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_odds_ratio_raw :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  0<x*y -> Admissions.admission_odds_ratio (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j*n/(x*y).
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  intro Hxy.
  unfold Admissions.admission_odds_ratio; simpl; field; nra.
Qed.

(**
 [normalized_four_second_given_first] (theorem) — Among successful first-route admissions within a stratum, the conditional second-route admission rate is joint over first-row mass.
 Mathematical meaning: Among successful first-route admissions within a stratum, the conditional second-route admission rate is joint over first-row mass.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), 0<j+x -> Admissions.conditional_B_given_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j/(j+x).
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_second_given_first :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  0<j+x -> Admissions.conditional_B_given_A (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j/(j+x).
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  intro Hrow.
  unfold Admissions.conditional_B_given_A, Admissions.p_A; simpl; field; nra.
Qed.

(**
 [normalized_four_first_given_second] (theorem) — Among successful second-route admissions within a stratum, the conditional first-route admission rate is joint over second-column mass.
 Mathematical meaning: Among successful second-route admissions within a stratum, the conditional first-route admission rate is joint over second-column mass.
 Exact checked proposition: forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n), 0<j+y -> Admissions.conditional_A_given_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j/(j+y).
 Premises and side conditions: Four unnormalized contingency masses are
 nonnegative and their total is strictly positive; additional positive
 denominators are explicitly supplied wherever conditional probability or
 an odds ratio would otherwise be undefined in the probabilistic sense.
 Proof/definition method: Reduce through the single positive-total
 normalized_four_stratum and use the existing Admissions identities,
 Stdlib field/ring/real arithmetic and the explicitly proved stratum
 denominator positivity. No unproved stochastic principles are assumed.
 Library reuse: Admissions conditional/independence/covariance algebra;
 FiniteSum/FiniteUnion through ThreeTestAdmissions, and Stdlib.Reals,
 Lra, Psatz and Field; no extra four-cell summation implementation.
 Boundary: Exact finite conditioning, not Gaussian multivariate
 conditioning, normal tail estimates or psychometric empirical claims.
*)
Theorem normalized_four_first_given_second :
  forall (j x y n:R) (Hj:0<=j) (Hx:0<=x) (Hy:0<=y) (Hn:0<=n) (Ht:0<j+x+y+n),
  0<j+y -> Admissions.conditional_A_given_B (normalized_four_stratum j x y n Hj Hx Hy Hn Ht)=j/(j+y).
Proof.
  intros j x y n Hj Hx Hy Hn Ht.
  intro Hcolumn.
  unfold Admissions.conditional_A_given_B, Admissions.p_B; simpl; field; nra.
Qed.

(**
 [stratum_ab_c_yes_total_atoms] (theorem) — The mass of the C-pass conditioning stratum equals the sum of its four disjoint raw AB contingency-table cells.
 Mathematical meaning: The mass of the C-pass conditioning stratum equals the sum of its four disjoint raw AB contingency-table cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m=(mass3 m (true,true,true)+mass3 m (true,false,true)+mass3 m (false,true,true)+mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_total_atoms :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m=(mass3 m (true,true,true)+mass3 m (true,false,true)+mass3 m (false,true,true)+mass3 m (false,false,true)).
Proof.
  intros m H; triple_lra.
Qed.

(**
 [stratum_ab_c_yes_joint_scaled] (theorem) — The conditional joint AB probability multiplied by selection mass recovers its triple-test joint atom.
 Mathematical meaning: The conditional joint AB probability multiplied by selection mass recovers its triple-test joint atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_both (stratum_ab_c_yes m H)=mass3 m (true,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_joint_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_both (stratum_ab_c_yes m H)=mass3 m (true,true,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_joint_scaled.
Qed.

(**
 [stratum_ab_c_yes_only_first_scaled] (theorem) — The conditional first-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional first-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.only_A (stratum_ab_c_yes m H)=mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_only_first_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.only_A (stratum_ab_c_yes m H)=mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_only_first_scaled.
Qed.

(**
 [stratum_ab_c_yes_only_second_scaled] (theorem) — The conditional second-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional second-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.only_B (stratum_ab_c_yes m H)=mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_only_second_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.only_B (stratum_ab_c_yes m H)=mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_only_second_scaled.
Qed.

(**
 [stratum_ab_c_yes_neither_scaled] (theorem) — The conditional neither-AB-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Mathematical meaning: The conditional neither-AB-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.neither (stratum_ab_c_yes m H)=mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_neither_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.neither (stratum_ab_c_yes m H)=mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_neither_scaled.
Qed.

(**
 [stratum_ab_c_yes_first_marginal_scaled] (theorem) — The first-route conditional AB marginal is the selected first-row mass divided by the conditioning probability.
 Mathematical meaning: The first-route conditional AB marginal is the selected first-row mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_A (stratum_ab_c_yes m H)=mass3 m (true,true,true)+mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_first_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_A (stratum_ab_c_yes m H)=mass3 m (true,true,true)+mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_first_scaled.
Qed.

(**
 [stratum_ab_c_yes_second_marginal_scaled] (theorem) — The second-route conditional AB marginal is the selected second-column mass divided by the conditioning probability.
 Mathematical meaning: The second-route conditional AB marginal is the selected second-column mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_B (stratum_ab_c_yes m H)=mass3 m (true,true,true)+mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_second_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_B (stratum_ab_c_yes m H)=mass3 m (true,true,true)+mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_second_scaled.
Qed.

(**
 [stratum_ab_c_yes_union_scaled] (theorem) — The conditional probability of passing at least one AB route has the correct three-cell selection-mass numerator.
 Mathematical meaning: The conditional probability of passing at least one AB route has the correct three-cell selection-mass numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_either (stratum_ab_c_yes m H)=mass3 m (true,true,true)+mass3 m (true,false,true)+mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_union_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_either (stratum_ab_c_yes m H)=mass3 m (true,true,true)+mass3 m (true,false,true)+mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_union_scaled.
Qed.

(**
 [stratum_ab_c_yes_exclusive_scaled] (theorem) — The conditional probability of exactly one AB success has the sum of two exclusive selected atoms as numerator.
 Mathematical meaning: The conditional probability of exactly one AB success has the sum of two exclusive selected atoms as numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_exactly_one (stratum_ab_c_yes m H)=mass3 m (true,false,true)+mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_exclusive_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*Admissions.p_exactly_one (stratum_ab_c_yes m H)=mass3 m (true,false,true)+mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_exclusive_scaled.
Qed.

(**
 [stratum_ab_c_yes_association_scaled] (theorem) — The third-route selection probability squared times conditional AB association equals the determinant of the four unnormalized selected contingency cells.
 Mathematical meaning: The third-route selection probability squared times conditional AB association equals the determinant of the four unnormalized selected contingency cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*pC3 m*Admissions.admission_association (stratum_ab_c_yes m H)=mass3 m (true,true,true)*mass3 m (false,false,true)-mass3 m (true,false,true)*mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_association_scaled :
  forall (m:ThreeTestModel) (H:0<pC3 m), pC3 m*pC3 m*Admissions.admission_association (stratum_ab_c_yes m H)=mass3 m (true,true,true)*mass3 m (false,false,true)-mass3 m (true,false,true)*mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ab_c_yes_total_atoms m H).
    unfold stratum_ab_c_yes.
    apply normalized_four_association_scaled.
Qed.

(**
 [stratum_ab_c_yes_independent_iff_raw] (theorem) — Conditional AB independence given C=true holds exactly when selected concordant and discordant cell products agree.
 Mathematical meaning: Conditional AB independence given C=true holds exactly when selected concordant and discordant cell products agree.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), (Admissions.p_both (stratum_ab_c_yes m H)=Admissions.p_A (stratum_ab_c_yes m H)*Admissions.p_B (stratum_ab_c_yes m H) <-> mass3 m (true,true,true)*mass3 m (false,false,true)=mass3 m (true,false,true)*mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_independent_iff_raw :
  forall (m:ThreeTestModel) (H:0<pC3 m), (Admissions.p_both (stratum_ab_c_yes m H)=Admissions.p_A (stratum_ab_c_yes m H)*Admissions.p_B (stratum_ab_c_yes m H) <-> mass3 m (true,true,true)*mass3 m (false,false,true)=mass3 m (true,false,true)*mass3 m (false,true,true)).
Proof.
  intros m H.
    unfold stratum_ab_c_yes.
    apply normalized_four_independent_iff.
Qed.

(**
 [stratum_ab_c_yes_association_positive_iff_raw] (theorem) — The selected AB pair has positive conditional association precisely when its raw concordant determinant is positive.
 Mathematical meaning: The selected AB pair has positive conditional association precisely when its raw concordant determinant is positive.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), (0<Admissions.admission_association (stratum_ab_c_yes m H) <-> mass3 m (true,false,true)*mass3 m (false,true,true)<mass3 m (true,true,true)*mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_association_positive_iff_raw :
  forall (m:ThreeTestModel) (H:0<pC3 m), (0<Admissions.admission_association (stratum_ab_c_yes m H) <-> mass3 m (true,false,true)*mass3 m (false,true,true)<mass3 m (true,true,true)*mass3 m (false,false,true)).
Proof.
  intros m H.
    unfold stratum_ab_c_yes.
    apply normalized_four_positive_association_iff.
Qed.

(**
 [stratum_ab_c_yes_association_negative_iff_raw] (theorem) — The selected AB pair has negative conditional association precisely when its raw concordant determinant is negative.
 Mathematical meaning: The selected AB pair has negative conditional association precisely when its raw concordant determinant is negative.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), (Admissions.admission_association (stratum_ab_c_yes m H)<0 <-> mass3 m (true,true,true)*mass3 m (false,false,true)<mass3 m (true,false,true)*mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_association_negative_iff_raw :
  forall (m:ThreeTestModel) (H:0<pC3 m), (Admissions.admission_association (stratum_ab_c_yes m H)<0 <-> mass3 m (true,true,true)*mass3 m (false,false,true)<mass3 m (true,false,true)*mass3 m (false,true,true)).
Proof.
  intros m H.
    unfold stratum_ab_c_yes.
    apply normalized_four_negative_association_iff.
Qed.

(**
 [stratum_ab_c_yes_second_given_first] (theorem) — The second-route success probability conditional on first-route success within the C-pass stratum is the selected joint/first-row ratio.
 Mathematical meaning: The second-route success probability conditional on first-route success within the C-pass stratum is the selected joint/first-row ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), 0<mass3 m (true,true,true)+mass3 m (true,false,true) -> Admissions.conditional_B_given_A (stratum_ab_c_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_second_given_first :
  forall (m:ThreeTestModel) (H:0<pC3 m), 0<mass3 m (true,true,true)+mass3 m (true,false,true) -> Admissions.conditional_B_given_A (stratum_ab_c_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,false,true)).
Proof.
  intros m H Hrow.
    unfold stratum_ab_c_yes.
    apply normalized_four_second_given_first; exact Hrow.
Qed.

(**
 [stratum_ab_c_yes_first_given_second] (theorem) — The first-route success probability conditional on second-route success within the C-pass stratum is the selected joint/second-column ratio.
 Mathematical meaning: The first-route success probability conditional on second-route success within the C-pass stratum is the selected joint/second-column ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), 0<mass3 m (true,true,true)+mass3 m (false,true,true) -> Admissions.conditional_A_given_B (stratum_ab_c_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_first_given_second :
  forall (m:ThreeTestModel) (H:0<pC3 m), 0<mass3 m (true,true,true)+mass3 m (false,true,true) -> Admissions.conditional_A_given_B (stratum_ab_c_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (false,true,true)).
Proof.
  intros m H Hcolumn.
    unfold stratum_ab_c_yes.
    apply normalized_four_first_given_second; exact Hcolumn.
Qed.

(**
 [stratum_ab_c_yes_odds_ratio] (theorem) — The normalized AB odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Mathematical meaning: The normalized AB odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), 0<mass3 m (true,false,true)*mass3 m (false,true,true) -> Admissions.admission_odds_ratio (stratum_ab_c_yes m H)=(mass3 m (true,true,true)*mass3 m (false,false,true))/(mass3 m (true,false,true)*mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_odds_ratio :
  forall (m:ThreeTestModel) (H:0<pC3 m), 0<mass3 m (true,false,true)*mass3 m (false,true,true) -> Admissions.admission_odds_ratio (stratum_ab_c_yes m H)=(mass3 m (true,true,true)*mass3 m (false,false,true))/(mass3 m (true,false,true)*mass3 m (false,true,true)).
Proof.
  intros m H Hxy.
    unfold stratum_ab_c_yes.
    apply normalized_four_odds_ratio_raw; exact Hxy.
Qed.

(**
 [stratum_ab_c_yes_frechet_lower] (theorem) — Conditional overlap in the C-pass stratum satisfies the Fréchet lower bound for the projected AB pair.
 Mathematical meaning: Conditional overlap in the C-pass stratum satisfies the Fréchet lower bound for the projected AB pair.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pC3 m), Admissions.p_A (stratum_ab_c_yes m H)+Admissions.p_B (stratum_ab_c_yes m H)-1<=Admissions.p_both (stratum_ab_c_yes m H).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_yes_frechet_lower :
  forall (m:ThreeTestModel) (H:0<pC3 m), Admissions.p_A (stratum_ab_c_yes m H)+Admissions.p_B (stratum_ab_c_yes m H)-1<=Admissions.p_both (stratum_ab_c_yes m H).
Proof.
  intros m H.
    apply Admissions.frechet_lower_bound.
Qed.

(**
 [stratum_ab_c_no_total_atoms] (theorem) — The mass of the C-failure conditioning stratum equals the sum of its four disjoint raw AB contingency-table cells.
 Mathematical meaning: The mass of the C-failure conditioning stratum equals the sum of its four disjoint raw AB contingency-table cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), 1-pC3 m=(mass3 m (true,true,false)+mass3 m (true,false,false)+mass3 m (false,true,false)+mass3 m (false,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_total_atoms :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), 1-pC3 m=(mass3 m (true,true,false)+mass3 m (true,false,false)+mass3 m (false,true,false)+mass3 m (false,false,false)).
Proof.
  intros m H; triple_lra.
Qed.

(**
 [stratum_ab_c_no_joint_scaled] (theorem) — The conditional joint AB probability multiplied by selection mass recovers its triple-test joint atom.
 Mathematical meaning: The conditional joint AB probability multiplied by selection mass recovers its triple-test joint atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_both (stratum_ab_c_no m H)=mass3 m (true,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_joint_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_both (stratum_ab_c_no m H)=mass3 m (true,true,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_joint_scaled.
Qed.

(**
 [stratum_ab_c_no_only_first_scaled] (theorem) — The conditional first-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional first-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.only_A (stratum_ab_c_no m H)=mass3 m (true,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_only_first_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.only_A (stratum_ab_c_no m H)=mass3 m (true,false,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_only_first_scaled.
Qed.

(**
 [stratum_ab_c_no_only_second_scaled] (theorem) — The conditional second-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional second-only AB probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.only_B (stratum_ab_c_no m H)=mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_only_second_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.only_B (stratum_ab_c_no m H)=mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_only_second_scaled.
Qed.

(**
 [stratum_ab_c_no_neither_scaled] (theorem) — The conditional neither-AB-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Mathematical meaning: The conditional neither-AB-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.neither (stratum_ab_c_no m H)=mass3 m (false,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_neither_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.neither (stratum_ab_c_no m H)=mass3 m (false,false,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_neither_scaled.
Qed.

(**
 [stratum_ab_c_no_first_marginal_scaled] (theorem) — The first-route conditional AB marginal is the selected first-row mass divided by the conditioning probability.
 Mathematical meaning: The first-route conditional AB marginal is the selected first-row mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_A (stratum_ab_c_no m H)=mass3 m (true,true,false)+mass3 m (true,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_first_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_A (stratum_ab_c_no m H)=mass3 m (true,true,false)+mass3 m (true,false,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_first_scaled.
Qed.

(**
 [stratum_ab_c_no_second_marginal_scaled] (theorem) — The second-route conditional AB marginal is the selected second-column mass divided by the conditioning probability.
 Mathematical meaning: The second-route conditional AB marginal is the selected second-column mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_B (stratum_ab_c_no m H)=mass3 m (true,true,false)+mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_second_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_B (stratum_ab_c_no m H)=mass3 m (true,true,false)+mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_second_scaled.
Qed.

(**
 [stratum_ab_c_no_union_scaled] (theorem) — The conditional probability of passing at least one AB route has the correct three-cell selection-mass numerator.
 Mathematical meaning: The conditional probability of passing at least one AB route has the correct three-cell selection-mass numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_either (stratum_ab_c_no m H)=mass3 m (true,true,false)+mass3 m (true,false,false)+mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_union_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_either (stratum_ab_c_no m H)=mass3 m (true,true,false)+mass3 m (true,false,false)+mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_union_scaled.
Qed.

(**
 [stratum_ab_c_no_exclusive_scaled] (theorem) — The conditional probability of exactly one AB success has the sum of two exclusive selected atoms as numerator.
 Mathematical meaning: The conditional probability of exactly one AB success has the sum of two exclusive selected atoms as numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_exactly_one (stratum_ab_c_no m H)=mass3 m (true,false,false)+mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_exclusive_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*Admissions.p_exactly_one (stratum_ab_c_no m H)=mass3 m (true,false,false)+mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_exclusive_scaled.
Qed.

(**
 [stratum_ab_c_no_association_scaled] (theorem) — The third-route selection probability squared times conditional AB association equals the determinant of the four unnormalized selected contingency cells.
 Mathematical meaning: The third-route selection probability squared times conditional AB association equals the determinant of the four unnormalized selected contingency cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*(1-pC3 m)*Admissions.admission_association (stratum_ab_c_no m H)=mass3 m (true,true,false)*mass3 m (false,false,false)-mass3 m (true,false,false)*mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_association_scaled :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (1-pC3 m)*(1-pC3 m)*Admissions.admission_association (stratum_ab_c_no m H)=mass3 m (true,true,false)*mass3 m (false,false,false)-mass3 m (true,false,false)*mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_ab_c_no_total_atoms m H).
    unfold stratum_ab_c_no.
    apply normalized_four_association_scaled.
Qed.

(**
 [stratum_ab_c_no_independent_iff_raw] (theorem) — Conditional AB independence given C=false holds exactly when selected concordant and discordant cell products agree.
 Mathematical meaning: Conditional AB independence given C=false holds exactly when selected concordant and discordant cell products agree.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (Admissions.p_both (stratum_ab_c_no m H)=Admissions.p_A (stratum_ab_c_no m H)*Admissions.p_B (stratum_ab_c_no m H) <-> mass3 m (true,true,false)*mass3 m (false,false,false)=mass3 m (true,false,false)*mass3 m (false,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_independent_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (Admissions.p_both (stratum_ab_c_no m H)=Admissions.p_A (stratum_ab_c_no m H)*Admissions.p_B (stratum_ab_c_no m H) <-> mass3 m (true,true,false)*mass3 m (false,false,false)=mass3 m (true,false,false)*mass3 m (false,true,false)).
Proof.
  intros m H.
    unfold stratum_ab_c_no.
    apply normalized_four_independent_iff.
Qed.

(**
 [stratum_ab_c_no_association_positive_iff_raw] (theorem) — The selected AB pair has positive conditional association precisely when its raw concordant determinant is positive.
 Mathematical meaning: The selected AB pair has positive conditional association precisely when its raw concordant determinant is positive.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (0<Admissions.admission_association (stratum_ab_c_no m H) <-> mass3 m (true,false,false)*mass3 m (false,true,false)<mass3 m (true,true,false)*mass3 m (false,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_association_positive_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (0<Admissions.admission_association (stratum_ab_c_no m H) <-> mass3 m (true,false,false)*mass3 m (false,true,false)<mass3 m (true,true,false)*mass3 m (false,false,false)).
Proof.
  intros m H.
    unfold stratum_ab_c_no.
    apply normalized_four_positive_association_iff.
Qed.

(**
 [stratum_ab_c_no_association_negative_iff_raw] (theorem) — The selected AB pair has negative conditional association precisely when its raw concordant determinant is negative.
 Mathematical meaning: The selected AB pair has negative conditional association precisely when its raw concordant determinant is negative.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), (Admissions.admission_association (stratum_ab_c_no m H)<0 <-> mass3 m (true,true,false)*mass3 m (false,false,false)<mass3 m (true,false,false)*mass3 m (false,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_association_negative_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), (Admissions.admission_association (stratum_ab_c_no m H)<0 <-> mass3 m (true,true,false)*mass3 m (false,false,false)<mass3 m (true,false,false)*mass3 m (false,true,false)).
Proof.
  intros m H.
    unfold stratum_ab_c_no.
    apply normalized_four_negative_association_iff.
Qed.

(**
 [stratum_ab_c_no_second_given_first] (theorem) — The second-route success probability conditional on first-route success within the C-failure stratum is the selected joint/first-row ratio.
 Mathematical meaning: The second-route success probability conditional on first-route success within the C-failure stratum is the selected joint/first-row ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), 0<mass3 m (true,true,false)+mass3 m (true,false,false) -> Admissions.conditional_B_given_A (stratum_ab_c_no m H)=mass3 m (true,true,false)/(mass3 m (true,true,false)+mass3 m (true,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_second_given_first :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), 0<mass3 m (true,true,false)+mass3 m (true,false,false) -> Admissions.conditional_B_given_A (stratum_ab_c_no m H)=mass3 m (true,true,false)/(mass3 m (true,true,false)+mass3 m (true,false,false)).
Proof.
  intros m H Hrow.
    unfold stratum_ab_c_no.
    apply normalized_four_second_given_first; exact Hrow.
Qed.

(**
 [stratum_ab_c_no_first_given_second] (theorem) — The first-route success probability conditional on second-route success within the C-failure stratum is the selected joint/second-column ratio.
 Mathematical meaning: The first-route success probability conditional on second-route success within the C-failure stratum is the selected joint/second-column ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), 0<mass3 m (true,true,false)+mass3 m (false,true,false) -> Admissions.conditional_A_given_B (stratum_ab_c_no m H)=mass3 m (true,true,false)/(mass3 m (true,true,false)+mass3 m (false,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_first_given_second :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), 0<mass3 m (true,true,false)+mass3 m (false,true,false) -> Admissions.conditional_A_given_B (stratum_ab_c_no m H)=mass3 m (true,true,false)/(mass3 m (true,true,false)+mass3 m (false,true,false)).
Proof.
  intros m H Hcolumn.
    unfold stratum_ab_c_no.
    apply normalized_four_first_given_second; exact Hcolumn.
Qed.

(**
 [stratum_ab_c_no_odds_ratio] (theorem) — The normalized AB odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Mathematical meaning: The normalized AB odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), 0<mass3 m (true,false,false)*mass3 m (false,true,false) -> Admissions.admission_odds_ratio (stratum_ab_c_no m H)=(mass3 m (true,true,false)*mass3 m (false,false,false))/(mass3 m (true,false,false)*mass3 m (false,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_odds_ratio :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), 0<mass3 m (true,false,false)*mass3 m (false,true,false) -> Admissions.admission_odds_ratio (stratum_ab_c_no m H)=(mass3 m (true,true,false)*mass3 m (false,false,false))/(mass3 m (true,false,false)*mass3 m (false,true,false)).
Proof.
  intros m H Hxy.
    unfold stratum_ab_c_no.
    apply normalized_four_odds_ratio_raw; exact Hxy.
Qed.

(**
 [stratum_ab_c_no_frechet_lower] (theorem) — Conditional overlap in the C-failure stratum satisfies the Fréchet lower bound for the projected AB pair.
 Mathematical meaning: Conditional overlap in the C-failure stratum satisfies the Fréchet lower bound for the projected AB pair.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pC3 m), Admissions.p_A (stratum_ab_c_no m H)+Admissions.p_B (stratum_ab_c_no m H)-1<=Admissions.p_both (stratum_ab_c_no m H).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ab_c_no_frechet_lower :
  forall (m:ThreeTestModel) (H:0<1-pC3 m), Admissions.p_A (stratum_ab_c_no m H)+Admissions.p_B (stratum_ab_c_no m H)-1<=Admissions.p_both (stratum_ab_c_no m H).
Proof.
  intros m H.
    apply Admissions.frechet_lower_bound.
Qed.

(**
 [stratum_ac_b_yes_total_atoms] (theorem) — The mass of the B-pass conditioning stratum equals the sum of its four disjoint raw AC contingency-table cells.
 Mathematical meaning: The mass of the B-pass conditioning stratum equals the sum of its four disjoint raw AC contingency-table cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m=(mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (false,true,true)+mass3 m (false,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_total_atoms :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m=(mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (false,true,true)+mass3 m (false,true,false)).
Proof.
  intros m H; triple_lra.
Qed.

(**
 [stratum_ac_b_yes_joint_scaled] (theorem) — The conditional joint AC probability multiplied by selection mass recovers its triple-test joint atom.
 Mathematical meaning: The conditional joint AC probability multiplied by selection mass recovers its triple-test joint atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_both (stratum_ac_b_yes m H)=mass3 m (true,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_joint_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_both (stratum_ac_b_yes m H)=mass3 m (true,true,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_joint_scaled.
Qed.

(**
 [stratum_ac_b_yes_only_first_scaled] (theorem) — The conditional first-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional first-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.only_A (stratum_ac_b_yes m H)=mass3 m (true,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_only_first_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.only_A (stratum_ac_b_yes m H)=mass3 m (true,true,false).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_only_first_scaled.
Qed.

(**
 [stratum_ac_b_yes_only_second_scaled] (theorem) — The conditional second-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional second-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.only_B (stratum_ac_b_yes m H)=mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_only_second_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.only_B (stratum_ac_b_yes m H)=mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_only_second_scaled.
Qed.

(**
 [stratum_ac_b_yes_neither_scaled] (theorem) — The conditional neither-AC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Mathematical meaning: The conditional neither-AC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.neither (stratum_ac_b_yes m H)=mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_neither_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.neither (stratum_ac_b_yes m H)=mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_neither_scaled.
Qed.

(**
 [stratum_ac_b_yes_first_marginal_scaled] (theorem) — The first-route conditional AC marginal is the selected first-row mass divided by the conditioning probability.
 Mathematical meaning: The first-route conditional AC marginal is the selected first-row mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_A (stratum_ac_b_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_first_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_A (stratum_ac_b_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_first_scaled.
Qed.

(**
 [stratum_ac_b_yes_second_marginal_scaled] (theorem) — The second-route conditional AC marginal is the selected second-column mass divided by the conditioning probability.
 Mathematical meaning: The second-route conditional AC marginal is the selected second-column mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_B (stratum_ac_b_yes m H)=mass3 m (true,true,true)+mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_second_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_B (stratum_ac_b_yes m H)=mass3 m (true,true,true)+mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_second_scaled.
Qed.

(**
 [stratum_ac_b_yes_union_scaled] (theorem) — The conditional probability of passing at least one AC route has the correct three-cell selection-mass numerator.
 Mathematical meaning: The conditional probability of passing at least one AC route has the correct three-cell selection-mass numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_either (stratum_ac_b_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_union_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_either (stratum_ac_b_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_union_scaled.
Qed.

(**
 [stratum_ac_b_yes_exclusive_scaled] (theorem) — The conditional probability of exactly one AC success has the sum of two exclusive selected atoms as numerator.
 Mathematical meaning: The conditional probability of exactly one AC success has the sum of two exclusive selected atoms as numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_exactly_one (stratum_ac_b_yes m H)=mass3 m (true,true,false)+mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_exclusive_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*Admissions.p_exactly_one (stratum_ac_b_yes m H)=mass3 m (true,true,false)+mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_exclusive_scaled.
Qed.

(**
 [stratum_ac_b_yes_association_scaled] (theorem) — The third-route selection probability squared times conditional AC association equals the determinant of the four unnormalized selected contingency cells.
 Mathematical meaning: The third-route selection probability squared times conditional AC association equals the determinant of the four unnormalized selected contingency cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*pB3 m*Admissions.admission_association (stratum_ac_b_yes m H)=mass3 m (true,true,true)*mass3 m (false,true,false)-mass3 m (true,true,false)*mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_association_scaled :
  forall (m:ThreeTestModel) (H:0<pB3 m), pB3 m*pB3 m*Admissions.admission_association (stratum_ac_b_yes m H)=mass3 m (true,true,true)*mass3 m (false,true,false)-mass3 m (true,true,false)*mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_yes_total_atoms m H).
    unfold stratum_ac_b_yes.
    apply normalized_four_association_scaled.
Qed.

(**
 [stratum_ac_b_yes_independent_iff_raw] (theorem) — Conditional AC independence given B=true holds exactly when selected concordant and discordant cell products agree.
 Mathematical meaning: Conditional AC independence given B=true holds exactly when selected concordant and discordant cell products agree.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), (Admissions.p_both (stratum_ac_b_yes m H)=Admissions.p_A (stratum_ac_b_yes m H)*Admissions.p_B (stratum_ac_b_yes m H) <-> mass3 m (true,true,true)*mass3 m (false,true,false)=mass3 m (true,true,false)*mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_independent_iff_raw :
  forall (m:ThreeTestModel) (H:0<pB3 m), (Admissions.p_both (stratum_ac_b_yes m H)=Admissions.p_A (stratum_ac_b_yes m H)*Admissions.p_B (stratum_ac_b_yes m H) <-> mass3 m (true,true,true)*mass3 m (false,true,false)=mass3 m (true,true,false)*mass3 m (false,true,true)).
Proof.
  intros m H.
    unfold stratum_ac_b_yes.
    apply normalized_four_independent_iff.
Qed.

(**
 [stratum_ac_b_yes_association_positive_iff_raw] (theorem) — The selected AC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Mathematical meaning: The selected AC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), (0<Admissions.admission_association (stratum_ac_b_yes m H) <-> mass3 m (true,true,false)*mass3 m (false,true,true)<mass3 m (true,true,true)*mass3 m (false,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_association_positive_iff_raw :
  forall (m:ThreeTestModel) (H:0<pB3 m), (0<Admissions.admission_association (stratum_ac_b_yes m H) <-> mass3 m (true,true,false)*mass3 m (false,true,true)<mass3 m (true,true,true)*mass3 m (false,true,false)).
Proof.
  intros m H.
    unfold stratum_ac_b_yes.
    apply normalized_four_positive_association_iff.
Qed.

(**
 [stratum_ac_b_yes_association_negative_iff_raw] (theorem) — The selected AC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Mathematical meaning: The selected AC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), (Admissions.admission_association (stratum_ac_b_yes m H)<0 <-> mass3 m (true,true,true)*mass3 m (false,true,false)<mass3 m (true,true,false)*mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_association_negative_iff_raw :
  forall (m:ThreeTestModel) (H:0<pB3 m), (Admissions.admission_association (stratum_ac_b_yes m H)<0 <-> mass3 m (true,true,true)*mass3 m (false,true,false)<mass3 m (true,true,false)*mass3 m (false,true,true)).
Proof.
  intros m H.
    unfold stratum_ac_b_yes.
    apply normalized_four_negative_association_iff.
Qed.

(**
 [stratum_ac_b_yes_second_given_first] (theorem) — The second-route success probability conditional on first-route success within the B-pass stratum is the selected joint/first-row ratio.
 Mathematical meaning: The second-route success probability conditional on first-route success within the B-pass stratum is the selected joint/first-row ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), 0<mass3 m (true,true,true)+mass3 m (true,true,false) -> Admissions.conditional_B_given_A (stratum_ac_b_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_second_given_first :
  forall (m:ThreeTestModel) (H:0<pB3 m), 0<mass3 m (true,true,true)+mass3 m (true,true,false) -> Admissions.conditional_B_given_A (stratum_ac_b_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,true,false)).
Proof.
  intros m H Hrow.
    unfold stratum_ac_b_yes.
    apply normalized_four_second_given_first; exact Hrow.
Qed.

(**
 [stratum_ac_b_yes_first_given_second] (theorem) — The first-route success probability conditional on second-route success within the B-pass stratum is the selected joint/second-column ratio.
 Mathematical meaning: The first-route success probability conditional on second-route success within the B-pass stratum is the selected joint/second-column ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), 0<mass3 m (true,true,true)+mass3 m (false,true,true) -> Admissions.conditional_A_given_B (stratum_ac_b_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_first_given_second :
  forall (m:ThreeTestModel) (H:0<pB3 m), 0<mass3 m (true,true,true)+mass3 m (false,true,true) -> Admissions.conditional_A_given_B (stratum_ac_b_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (false,true,true)).
Proof.
  intros m H Hcolumn.
    unfold stratum_ac_b_yes.
    apply normalized_four_first_given_second; exact Hcolumn.
Qed.

(**
 [stratum_ac_b_yes_odds_ratio] (theorem) — The normalized AC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Mathematical meaning: The normalized AC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), 0<mass3 m (true,true,false)*mass3 m (false,true,true) -> Admissions.admission_odds_ratio (stratum_ac_b_yes m H)=(mass3 m (true,true,true)*mass3 m (false,true,false))/(mass3 m (true,true,false)*mass3 m (false,true,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_odds_ratio :
  forall (m:ThreeTestModel) (H:0<pB3 m), 0<mass3 m (true,true,false)*mass3 m (false,true,true) -> Admissions.admission_odds_ratio (stratum_ac_b_yes m H)=(mass3 m (true,true,true)*mass3 m (false,true,false))/(mass3 m (true,true,false)*mass3 m (false,true,true)).
Proof.
  intros m H Hxy.
    unfold stratum_ac_b_yes.
    apply normalized_four_odds_ratio_raw; exact Hxy.
Qed.

(**
 [stratum_ac_b_yes_frechet_lower] (theorem) — Conditional overlap in the B-pass stratum satisfies the Fréchet lower bound for the projected AC pair.
 Mathematical meaning: Conditional overlap in the B-pass stratum satisfies the Fréchet lower bound for the projected AC pair.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pB3 m), Admissions.p_A (stratum_ac_b_yes m H)+Admissions.p_B (stratum_ac_b_yes m H)-1<=Admissions.p_both (stratum_ac_b_yes m H).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_yes_frechet_lower :
  forall (m:ThreeTestModel) (H:0<pB3 m), Admissions.p_A (stratum_ac_b_yes m H)+Admissions.p_B (stratum_ac_b_yes m H)-1<=Admissions.p_both (stratum_ac_b_yes m H).
Proof.
  intros m H.
    apply Admissions.frechet_lower_bound.
Qed.

(**
 [stratum_ac_b_no_total_atoms] (theorem) — The mass of the B-failure conditioning stratum equals the sum of its four disjoint raw AC contingency-table cells.
 Mathematical meaning: The mass of the B-failure conditioning stratum equals the sum of its four disjoint raw AC contingency-table cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), 1-pB3 m=(mass3 m (true,false,true)+mass3 m (true,false,false)+mass3 m (false,false,true)+mass3 m (false,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_total_atoms :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), 1-pB3 m=(mass3 m (true,false,true)+mass3 m (true,false,false)+mass3 m (false,false,true)+mass3 m (false,false,false)).
Proof.
  intros m H; triple_lra.
Qed.

(**
 [stratum_ac_b_no_joint_scaled] (theorem) — The conditional joint AC probability multiplied by selection mass recovers its triple-test joint atom.
 Mathematical meaning: The conditional joint AC probability multiplied by selection mass recovers its triple-test joint atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_both (stratum_ac_b_no m H)=mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_joint_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_both (stratum_ac_b_no m H)=mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_joint_scaled.
Qed.

(**
 [stratum_ac_b_no_only_first_scaled] (theorem) — The conditional first-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional first-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.only_A (stratum_ac_b_no m H)=mass3 m (true,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_only_first_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.only_A (stratum_ac_b_no m H)=mass3 m (true,false,false).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_only_first_scaled.
Qed.

(**
 [stratum_ac_b_no_only_second_scaled] (theorem) — The conditional second-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional second-only AC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.only_B (stratum_ac_b_no m H)=mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_only_second_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.only_B (stratum_ac_b_no m H)=mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_only_second_scaled.
Qed.

(**
 [stratum_ac_b_no_neither_scaled] (theorem) — The conditional neither-AC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Mathematical meaning: The conditional neither-AC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.neither (stratum_ac_b_no m H)=mass3 m (false,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_neither_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.neither (stratum_ac_b_no m H)=mass3 m (false,false,false).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_neither_scaled.
Qed.

(**
 [stratum_ac_b_no_first_marginal_scaled] (theorem) — The first-route conditional AC marginal is the selected first-row mass divided by the conditioning probability.
 Mathematical meaning: The first-route conditional AC marginal is the selected first-row mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_A (stratum_ac_b_no m H)=mass3 m (true,false,true)+mass3 m (true,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_first_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_A (stratum_ac_b_no m H)=mass3 m (true,false,true)+mass3 m (true,false,false).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_first_scaled.
Qed.

(**
 [stratum_ac_b_no_second_marginal_scaled] (theorem) — The second-route conditional AC marginal is the selected second-column mass divided by the conditioning probability.
 Mathematical meaning: The second-route conditional AC marginal is the selected second-column mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_B (stratum_ac_b_no m H)=mass3 m (true,false,true)+mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_second_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_B (stratum_ac_b_no m H)=mass3 m (true,false,true)+mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_second_scaled.
Qed.

(**
 [stratum_ac_b_no_union_scaled] (theorem) — The conditional probability of passing at least one AC route has the correct three-cell selection-mass numerator.
 Mathematical meaning: The conditional probability of passing at least one AC route has the correct three-cell selection-mass numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_either (stratum_ac_b_no m H)=mass3 m (true,false,true)+mass3 m (true,false,false)+mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_union_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_either (stratum_ac_b_no m H)=mass3 m (true,false,true)+mass3 m (true,false,false)+mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_union_scaled.
Qed.

(**
 [stratum_ac_b_no_exclusive_scaled] (theorem) — The conditional probability of exactly one AC success has the sum of two exclusive selected atoms as numerator.
 Mathematical meaning: The conditional probability of exactly one AC success has the sum of two exclusive selected atoms as numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_exactly_one (stratum_ac_b_no m H)=mass3 m (true,false,false)+mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_exclusive_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*Admissions.p_exactly_one (stratum_ac_b_no m H)=mass3 m (true,false,false)+mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_exclusive_scaled.
Qed.

(**
 [stratum_ac_b_no_association_scaled] (theorem) — The third-route selection probability squared times conditional AC association equals the determinant of the four unnormalized selected contingency cells.
 Mathematical meaning: The third-route selection probability squared times conditional AC association equals the determinant of the four unnormalized selected contingency cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*(1-pB3 m)*Admissions.admission_association (stratum_ac_b_no m H)=mass3 m (true,false,true)*mass3 m (false,false,false)-mass3 m (true,false,false)*mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_association_scaled :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (1-pB3 m)*(1-pB3 m)*Admissions.admission_association (stratum_ac_b_no m H)=mass3 m (true,false,true)*mass3 m (false,false,false)-mass3 m (true,false,false)*mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_ac_b_no_total_atoms m H).
    unfold stratum_ac_b_no.
    apply normalized_four_association_scaled.
Qed.

(**
 [stratum_ac_b_no_independent_iff_raw] (theorem) — Conditional AC independence given B=false holds exactly when selected concordant and discordant cell products agree.
 Mathematical meaning: Conditional AC independence given B=false holds exactly when selected concordant and discordant cell products agree.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (Admissions.p_both (stratum_ac_b_no m H)=Admissions.p_A (stratum_ac_b_no m H)*Admissions.p_B (stratum_ac_b_no m H) <-> mass3 m (true,false,true)*mass3 m (false,false,false)=mass3 m (true,false,false)*mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_independent_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (Admissions.p_both (stratum_ac_b_no m H)=Admissions.p_A (stratum_ac_b_no m H)*Admissions.p_B (stratum_ac_b_no m H) <-> mass3 m (true,false,true)*mass3 m (false,false,false)=mass3 m (true,false,false)*mass3 m (false,false,true)).
Proof.
  intros m H.
    unfold stratum_ac_b_no.
    apply normalized_four_independent_iff.
Qed.

(**
 [stratum_ac_b_no_association_positive_iff_raw] (theorem) — The selected AC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Mathematical meaning: The selected AC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (0<Admissions.admission_association (stratum_ac_b_no m H) <-> mass3 m (true,false,false)*mass3 m (false,false,true)<mass3 m (true,false,true)*mass3 m (false,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_association_positive_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (0<Admissions.admission_association (stratum_ac_b_no m H) <-> mass3 m (true,false,false)*mass3 m (false,false,true)<mass3 m (true,false,true)*mass3 m (false,false,false)).
Proof.
  intros m H.
    unfold stratum_ac_b_no.
    apply normalized_four_positive_association_iff.
Qed.

(**
 [stratum_ac_b_no_association_negative_iff_raw] (theorem) — The selected AC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Mathematical meaning: The selected AC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), (Admissions.admission_association (stratum_ac_b_no m H)<0 <-> mass3 m (true,false,true)*mass3 m (false,false,false)<mass3 m (true,false,false)*mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_association_negative_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), (Admissions.admission_association (stratum_ac_b_no m H)<0 <-> mass3 m (true,false,true)*mass3 m (false,false,false)<mass3 m (true,false,false)*mass3 m (false,false,true)).
Proof.
  intros m H.
    unfold stratum_ac_b_no.
    apply normalized_four_negative_association_iff.
Qed.

(**
 [stratum_ac_b_no_second_given_first] (theorem) — The second-route success probability conditional on first-route success within the B-failure stratum is the selected joint/first-row ratio.
 Mathematical meaning: The second-route success probability conditional on first-route success within the B-failure stratum is the selected joint/first-row ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), 0<mass3 m (true,false,true)+mass3 m (true,false,false) -> Admissions.conditional_B_given_A (stratum_ac_b_no m H)=mass3 m (true,false,true)/(mass3 m (true,false,true)+mass3 m (true,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_second_given_first :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), 0<mass3 m (true,false,true)+mass3 m (true,false,false) -> Admissions.conditional_B_given_A (stratum_ac_b_no m H)=mass3 m (true,false,true)/(mass3 m (true,false,true)+mass3 m (true,false,false)).
Proof.
  intros m H Hrow.
    unfold stratum_ac_b_no.
    apply normalized_four_second_given_first; exact Hrow.
Qed.

(**
 [stratum_ac_b_no_first_given_second] (theorem) — The first-route success probability conditional on second-route success within the B-failure stratum is the selected joint/second-column ratio.
 Mathematical meaning: The first-route success probability conditional on second-route success within the B-failure stratum is the selected joint/second-column ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), 0<mass3 m (true,false,true)+mass3 m (false,false,true) -> Admissions.conditional_A_given_B (stratum_ac_b_no m H)=mass3 m (true,false,true)/(mass3 m (true,false,true)+mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_first_given_second :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), 0<mass3 m (true,false,true)+mass3 m (false,false,true) -> Admissions.conditional_A_given_B (stratum_ac_b_no m H)=mass3 m (true,false,true)/(mass3 m (true,false,true)+mass3 m (false,false,true)).
Proof.
  intros m H Hcolumn.
    unfold stratum_ac_b_no.
    apply normalized_four_first_given_second; exact Hcolumn.
Qed.

(**
 [stratum_ac_b_no_odds_ratio] (theorem) — The normalized AC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Mathematical meaning: The normalized AC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), 0<mass3 m (true,false,false)*mass3 m (false,false,true) -> Admissions.admission_odds_ratio (stratum_ac_b_no m H)=(mass3 m (true,false,true)*mass3 m (false,false,false))/(mass3 m (true,false,false)*mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_odds_ratio :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), 0<mass3 m (true,false,false)*mass3 m (false,false,true) -> Admissions.admission_odds_ratio (stratum_ac_b_no m H)=(mass3 m (true,false,true)*mass3 m (false,false,false))/(mass3 m (true,false,false)*mass3 m (false,false,true)).
Proof.
  intros m H Hxy.
    unfold stratum_ac_b_no.
    apply normalized_four_odds_ratio_raw; exact Hxy.
Qed.

(**
 [stratum_ac_b_no_frechet_lower] (theorem) — Conditional overlap in the B-failure stratum satisfies the Fréchet lower bound for the projected AC pair.
 Mathematical meaning: Conditional overlap in the B-failure stratum satisfies the Fréchet lower bound for the projected AC pair.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pB3 m), Admissions.p_A (stratum_ac_b_no m H)+Admissions.p_B (stratum_ac_b_no m H)-1<=Admissions.p_both (stratum_ac_b_no m H).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_ac_b_no_frechet_lower :
  forall (m:ThreeTestModel) (H:0<1-pB3 m), Admissions.p_A (stratum_ac_b_no m H)+Admissions.p_B (stratum_ac_b_no m H)-1<=Admissions.p_both (stratum_ac_b_no m H).
Proof.
  intros m H.
    apply Admissions.frechet_lower_bound.
Qed.

(**
 [stratum_bc_a_yes_total_atoms] (theorem) — The mass of the A-pass conditioning stratum equals the sum of its four disjoint raw BC contingency-table cells.
 Mathematical meaning: The mass of the A-pass conditioning stratum equals the sum of its four disjoint raw BC contingency-table cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m=(mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (true,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_total_atoms :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m=(mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (true,false,false)).
Proof.
  intros m H; triple_lra.
Qed.

(**
 [stratum_bc_a_yes_joint_scaled] (theorem) — The conditional joint BC probability multiplied by selection mass recovers its triple-test joint atom.
 Mathematical meaning: The conditional joint BC probability multiplied by selection mass recovers its triple-test joint atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_both (stratum_bc_a_yes m H)=mass3 m (true,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_joint_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_both (stratum_bc_a_yes m H)=mass3 m (true,true,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_joint_scaled.
Qed.

(**
 [stratum_bc_a_yes_only_first_scaled] (theorem) — The conditional first-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional first-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.only_A (stratum_bc_a_yes m H)=mass3 m (true,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_only_first_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.only_A (stratum_bc_a_yes m H)=mass3 m (true,true,false).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_only_first_scaled.
Qed.

(**
 [stratum_bc_a_yes_only_second_scaled] (theorem) — The conditional second-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional second-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.only_B (stratum_bc_a_yes m H)=mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_only_second_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.only_B (stratum_bc_a_yes m H)=mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_only_second_scaled.
Qed.

(**
 [stratum_bc_a_yes_neither_scaled] (theorem) — The conditional neither-BC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Mathematical meaning: The conditional neither-BC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.neither (stratum_bc_a_yes m H)=mass3 m (true,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_neither_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.neither (stratum_bc_a_yes m H)=mass3 m (true,false,false).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_neither_scaled.
Qed.

(**
 [stratum_bc_a_yes_first_marginal_scaled] (theorem) — The first-route conditional BC marginal is the selected first-row mass divided by the conditioning probability.
 Mathematical meaning: The first-route conditional BC marginal is the selected first-row mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_A (stratum_bc_a_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_first_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_A (stratum_bc_a_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_first_scaled.
Qed.

(**
 [stratum_bc_a_yes_second_marginal_scaled] (theorem) — The second-route conditional BC marginal is the selected second-column mass divided by the conditioning probability.
 Mathematical meaning: The second-route conditional BC marginal is the selected second-column mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_B (stratum_bc_a_yes m H)=mass3 m (true,true,true)+mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_second_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_B (stratum_bc_a_yes m H)=mass3 m (true,true,true)+mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_second_scaled.
Qed.

(**
 [stratum_bc_a_yes_union_scaled] (theorem) — The conditional probability of passing at least one BC route has the correct three-cell selection-mass numerator.
 Mathematical meaning: The conditional probability of passing at least one BC route has the correct three-cell selection-mass numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_either (stratum_bc_a_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_union_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_either (stratum_bc_a_yes m H)=mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_union_scaled.
Qed.

(**
 [stratum_bc_a_yes_exclusive_scaled] (theorem) — The conditional probability of exactly one BC success has the sum of two exclusive selected atoms as numerator.
 Mathematical meaning: The conditional probability of exactly one BC success has the sum of two exclusive selected atoms as numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_exactly_one (stratum_bc_a_yes m H)=mass3 m (true,true,false)+mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_exclusive_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*Admissions.p_exactly_one (stratum_bc_a_yes m H)=mass3 m (true,true,false)+mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_exclusive_scaled.
Qed.

(**
 [stratum_bc_a_yes_association_scaled] (theorem) — The third-route selection probability squared times conditional BC association equals the determinant of the four unnormalized selected contingency cells.
 Mathematical meaning: The third-route selection probability squared times conditional BC association equals the determinant of the four unnormalized selected contingency cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*pA3 m*Admissions.admission_association (stratum_bc_a_yes m H)=mass3 m (true,true,true)*mass3 m (true,false,false)-mass3 m (true,true,false)*mass3 m (true,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_association_scaled :
  forall (m:ThreeTestModel) (H:0<pA3 m), pA3 m*pA3 m*Admissions.admission_association (stratum_bc_a_yes m H)=mass3 m (true,true,true)*mass3 m (true,false,false)-mass3 m (true,true,false)*mass3 m (true,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_yes_total_atoms m H).
    unfold stratum_bc_a_yes.
    apply normalized_four_association_scaled.
Qed.

(**
 [stratum_bc_a_yes_independent_iff_raw] (theorem) — Conditional BC independence given A=true holds exactly when selected concordant and discordant cell products agree.
 Mathematical meaning: Conditional BC independence given A=true holds exactly when selected concordant and discordant cell products agree.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), (Admissions.p_both (stratum_bc_a_yes m H)=Admissions.p_A (stratum_bc_a_yes m H)*Admissions.p_B (stratum_bc_a_yes m H) <-> mass3 m (true,true,true)*mass3 m (true,false,false)=mass3 m (true,true,false)*mass3 m (true,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_independent_iff_raw :
  forall (m:ThreeTestModel) (H:0<pA3 m), (Admissions.p_both (stratum_bc_a_yes m H)=Admissions.p_A (stratum_bc_a_yes m H)*Admissions.p_B (stratum_bc_a_yes m H) <-> mass3 m (true,true,true)*mass3 m (true,false,false)=mass3 m (true,true,false)*mass3 m (true,false,true)).
Proof.
  intros m H.
    unfold stratum_bc_a_yes.
    apply normalized_four_independent_iff.
Qed.

(**
 [stratum_bc_a_yes_association_positive_iff_raw] (theorem) — The selected BC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Mathematical meaning: The selected BC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), (0<Admissions.admission_association (stratum_bc_a_yes m H) <-> mass3 m (true,true,false)*mass3 m (true,false,true)<mass3 m (true,true,true)*mass3 m (true,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_association_positive_iff_raw :
  forall (m:ThreeTestModel) (H:0<pA3 m), (0<Admissions.admission_association (stratum_bc_a_yes m H) <-> mass3 m (true,true,false)*mass3 m (true,false,true)<mass3 m (true,true,true)*mass3 m (true,false,false)).
Proof.
  intros m H.
    unfold stratum_bc_a_yes.
    apply normalized_four_positive_association_iff.
Qed.

(**
 [stratum_bc_a_yes_association_negative_iff_raw] (theorem) — The selected BC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Mathematical meaning: The selected BC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), (Admissions.admission_association (stratum_bc_a_yes m H)<0 <-> mass3 m (true,true,true)*mass3 m (true,false,false)<mass3 m (true,true,false)*mass3 m (true,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_association_negative_iff_raw :
  forall (m:ThreeTestModel) (H:0<pA3 m), (Admissions.admission_association (stratum_bc_a_yes m H)<0 <-> mass3 m (true,true,true)*mass3 m (true,false,false)<mass3 m (true,true,false)*mass3 m (true,false,true)).
Proof.
  intros m H.
    unfold stratum_bc_a_yes.
    apply normalized_four_negative_association_iff.
Qed.

(**
 [stratum_bc_a_yes_second_given_first] (theorem) — The second-route success probability conditional on first-route success within the A-pass stratum is the selected joint/first-row ratio.
 Mathematical meaning: The second-route success probability conditional on first-route success within the A-pass stratum is the selected joint/first-row ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), 0<mass3 m (true,true,true)+mass3 m (true,true,false) -> Admissions.conditional_B_given_A (stratum_bc_a_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_second_given_first :
  forall (m:ThreeTestModel) (H:0<pA3 m), 0<mass3 m (true,true,true)+mass3 m (true,true,false) -> Admissions.conditional_B_given_A (stratum_bc_a_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,true,false)).
Proof.
  intros m H Hrow.
    unfold stratum_bc_a_yes.
    apply normalized_four_second_given_first; exact Hrow.
Qed.

(**
 [stratum_bc_a_yes_first_given_second] (theorem) — The first-route success probability conditional on second-route success within the A-pass stratum is the selected joint/second-column ratio.
 Mathematical meaning: The first-route success probability conditional on second-route success within the A-pass stratum is the selected joint/second-column ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), 0<mass3 m (true,true,true)+mass3 m (true,false,true) -> Admissions.conditional_A_given_B (stratum_bc_a_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_first_given_second :
  forall (m:ThreeTestModel) (H:0<pA3 m), 0<mass3 m (true,true,true)+mass3 m (true,false,true) -> Admissions.conditional_A_given_B (stratum_bc_a_yes m H)=mass3 m (true,true,true)/(mass3 m (true,true,true)+mass3 m (true,false,true)).
Proof.
  intros m H Hcolumn.
    unfold stratum_bc_a_yes.
    apply normalized_four_first_given_second; exact Hcolumn.
Qed.

(**
 [stratum_bc_a_yes_odds_ratio] (theorem) — The normalized BC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Mathematical meaning: The normalized BC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), 0<mass3 m (true,true,false)*mass3 m (true,false,true) -> Admissions.admission_odds_ratio (stratum_bc_a_yes m H)=(mass3 m (true,true,true)*mass3 m (true,false,false))/(mass3 m (true,true,false)*mass3 m (true,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_odds_ratio :
  forall (m:ThreeTestModel) (H:0<pA3 m), 0<mass3 m (true,true,false)*mass3 m (true,false,true) -> Admissions.admission_odds_ratio (stratum_bc_a_yes m H)=(mass3 m (true,true,true)*mass3 m (true,false,false))/(mass3 m (true,true,false)*mass3 m (true,false,true)).
Proof.
  intros m H Hxy.
    unfold stratum_bc_a_yes.
    apply normalized_four_odds_ratio_raw; exact Hxy.
Qed.

(**
 [stratum_bc_a_yes_frechet_lower] (theorem) — Conditional overlap in the A-pass stratum satisfies the Fréchet lower bound for the projected BC pair.
 Mathematical meaning: Conditional overlap in the A-pass stratum satisfies the Fréchet lower bound for the projected BC pair.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<pA3 m), Admissions.p_A (stratum_bc_a_yes m H)+Admissions.p_B (stratum_bc_a_yes m H)-1<=Admissions.p_both (stratum_bc_a_yes m H).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_yes_frechet_lower :
  forall (m:ThreeTestModel) (H:0<pA3 m), Admissions.p_A (stratum_bc_a_yes m H)+Admissions.p_B (stratum_bc_a_yes m H)-1<=Admissions.p_both (stratum_bc_a_yes m H).
Proof.
  intros m H.
    apply Admissions.frechet_lower_bound.
Qed.

(**
 [stratum_bc_a_no_total_atoms] (theorem) — The mass of the A-failure conditioning stratum equals the sum of its four disjoint raw BC contingency-table cells.
 Mathematical meaning: The mass of the A-failure conditioning stratum equals the sum of its four disjoint raw BC contingency-table cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), 1-pA3 m=(mass3 m (false,true,true)+mass3 m (false,true,false)+mass3 m (false,false,true)+mass3 m (false,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_total_atoms :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), 1-pA3 m=(mass3 m (false,true,true)+mass3 m (false,true,false)+mass3 m (false,false,true)+mass3 m (false,false,false)).
Proof.
  intros m H; triple_lra.
Qed.

(**
 [stratum_bc_a_no_joint_scaled] (theorem) — The conditional joint BC probability multiplied by selection mass recovers its triple-test joint atom.
 Mathematical meaning: The conditional joint BC probability multiplied by selection mass recovers its triple-test joint atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_both (stratum_bc_a_no m H)=mass3 m (false,true,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_joint_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_both (stratum_bc_a_no m H)=mass3 m (false,true,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_joint_scaled.
Qed.

(**
 [stratum_bc_a_no_only_first_scaled] (theorem) — The conditional first-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional first-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.only_A (stratum_bc_a_no m H)=mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_only_first_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.only_A (stratum_bc_a_no m H)=mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_only_first_scaled.
Qed.

(**
 [stratum_bc_a_no_only_second_scaled] (theorem) — The conditional second-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Mathematical meaning: The conditional second-only BC probability multiplied by selection mass recovers its raw selected exclusive atom.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.only_B (stratum_bc_a_no m H)=mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_only_second_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.only_B (stratum_bc_a_no m H)=mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_only_second_scaled.
Qed.

(**
 [stratum_bc_a_no_neither_scaled] (theorem) — The conditional neither-BC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Mathematical meaning: The conditional neither-BC-route mass, scaled by the third-route stratum probability, recovers its raw all-rejected cell.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.neither (stratum_bc_a_no m H)=mass3 m (false,false,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_neither_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.neither (stratum_bc_a_no m H)=mass3 m (false,false,false).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_neither_scaled.
Qed.

(**
 [stratum_bc_a_no_first_marginal_scaled] (theorem) — The first-route conditional BC marginal is the selected first-row mass divided by the conditioning probability.
 Mathematical meaning: The first-route conditional BC marginal is the selected first-row mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_A (stratum_bc_a_no m H)=mass3 m (false,true,true)+mass3 m (false,true,false).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_first_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_A (stratum_bc_a_no m H)=mass3 m (false,true,true)+mass3 m (false,true,false).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_first_scaled.
Qed.

(**
 [stratum_bc_a_no_second_marginal_scaled] (theorem) — The second-route conditional BC marginal is the selected second-column mass divided by the conditioning probability.
 Mathematical meaning: The second-route conditional BC marginal is the selected second-column mass divided by the conditioning probability.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_B (stratum_bc_a_no m H)=mass3 m (false,true,true)+mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_second_marginal_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_B (stratum_bc_a_no m H)=mass3 m (false,true,true)+mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_second_scaled.
Qed.

(**
 [stratum_bc_a_no_union_scaled] (theorem) — The conditional probability of passing at least one BC route has the correct three-cell selection-mass numerator.
 Mathematical meaning: The conditional probability of passing at least one BC route has the correct three-cell selection-mass numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_either (stratum_bc_a_no m H)=mass3 m (false,true,true)+mass3 m (false,true,false)+mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_union_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_either (stratum_bc_a_no m H)=mass3 m (false,true,true)+mass3 m (false,true,false)+mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_union_scaled.
Qed.

(**
 [stratum_bc_a_no_exclusive_scaled] (theorem) — The conditional probability of exactly one BC success has the sum of two exclusive selected atoms as numerator.
 Mathematical meaning: The conditional probability of exactly one BC success has the sum of two exclusive selected atoms as numerator.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_exactly_one (stratum_bc_a_no m H)=mass3 m (false,true,false)+mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_exclusive_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*Admissions.p_exactly_one (stratum_bc_a_no m H)=mass3 m (false,true,false)+mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_exclusive_scaled.
Qed.

(**
 [stratum_bc_a_no_association_scaled] (theorem) — The third-route selection probability squared times conditional BC association equals the determinant of the four unnormalized selected contingency cells.
 Mathematical meaning: The third-route selection probability squared times conditional BC association equals the determinant of the four unnormalized selected contingency cells.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*(1-pA3 m)*Admissions.admission_association (stratum_bc_a_no m H)=mass3 m (false,true,true)*mass3 m (false,false,false)-mass3 m (false,true,false)*mass3 m (false,false,true).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_association_scaled :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (1-pA3 m)*(1-pA3 m)*Admissions.admission_association (stratum_bc_a_no m H)=mass3 m (false,true,true)*mass3 m (false,false,false)-mass3 m (false,true,false)*mass3 m (false,false,true).
Proof.
  intros m H.
    rewrite (stratum_bc_a_no_total_atoms m H).
    unfold stratum_bc_a_no.
    apply normalized_four_association_scaled.
Qed.

(**
 [stratum_bc_a_no_independent_iff_raw] (theorem) — Conditional BC independence given A=false holds exactly when selected concordant and discordant cell products agree.
 Mathematical meaning: Conditional BC independence given A=false holds exactly when selected concordant and discordant cell products agree.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (Admissions.p_both (stratum_bc_a_no m H)=Admissions.p_A (stratum_bc_a_no m H)*Admissions.p_B (stratum_bc_a_no m H) <-> mass3 m (false,true,true)*mass3 m (false,false,false)=mass3 m (false,true,false)*mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_independent_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (Admissions.p_both (stratum_bc_a_no m H)=Admissions.p_A (stratum_bc_a_no m H)*Admissions.p_B (stratum_bc_a_no m H) <-> mass3 m (false,true,true)*mass3 m (false,false,false)=mass3 m (false,true,false)*mass3 m (false,false,true)).
Proof.
  intros m H.
    unfold stratum_bc_a_no.
    apply normalized_four_independent_iff.
Qed.

(**
 [stratum_bc_a_no_association_positive_iff_raw] (theorem) — The selected BC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Mathematical meaning: The selected BC pair has positive conditional association precisely when its raw concordant determinant is positive.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (0<Admissions.admission_association (stratum_bc_a_no m H) <-> mass3 m (false,true,false)*mass3 m (false,false,true)<mass3 m (false,true,true)*mass3 m (false,false,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_association_positive_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (0<Admissions.admission_association (stratum_bc_a_no m H) <-> mass3 m (false,true,false)*mass3 m (false,false,true)<mass3 m (false,true,true)*mass3 m (false,false,false)).
Proof.
  intros m H.
    unfold stratum_bc_a_no.
    apply normalized_four_positive_association_iff.
Qed.

(**
 [stratum_bc_a_no_association_negative_iff_raw] (theorem) — The selected BC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Mathematical meaning: The selected BC pair has negative conditional association precisely when its raw concordant determinant is negative.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), (Admissions.admission_association (stratum_bc_a_no m H)<0 <-> mass3 m (false,true,true)*mass3 m (false,false,false)<mass3 m (false,true,false)*mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_association_negative_iff_raw :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), (Admissions.admission_association (stratum_bc_a_no m H)<0 <-> mass3 m (false,true,true)*mass3 m (false,false,false)<mass3 m (false,true,false)*mass3 m (false,false,true)).
Proof.
  intros m H.
    unfold stratum_bc_a_no.
    apply normalized_four_negative_association_iff.
Qed.

(**
 [stratum_bc_a_no_second_given_first] (theorem) — The second-route success probability conditional on first-route success within the A-failure stratum is the selected joint/first-row ratio.
 Mathematical meaning: The second-route success probability conditional on first-route success within the A-failure stratum is the selected joint/first-row ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), 0<mass3 m (false,true,true)+mass3 m (false,true,false) -> Admissions.conditional_B_given_A (stratum_bc_a_no m H)=mass3 m (false,true,true)/(mass3 m (false,true,true)+mass3 m (false,true,false)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_second_given_first :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), 0<mass3 m (false,true,true)+mass3 m (false,true,false) -> Admissions.conditional_B_given_A (stratum_bc_a_no m H)=mass3 m (false,true,true)/(mass3 m (false,true,true)+mass3 m (false,true,false)).
Proof.
  intros m H Hrow.
    unfold stratum_bc_a_no.
    apply normalized_four_second_given_first; exact Hrow.
Qed.

(**
 [stratum_bc_a_no_first_given_second] (theorem) — The first-route success probability conditional on second-route success within the A-failure stratum is the selected joint/second-column ratio.
 Mathematical meaning: The first-route success probability conditional on second-route success within the A-failure stratum is the selected joint/second-column ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), 0<mass3 m (false,true,true)+mass3 m (false,false,true) -> Admissions.conditional_A_given_B (stratum_bc_a_no m H)=mass3 m (false,true,true)/(mass3 m (false,true,true)+mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_first_given_second :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), 0<mass3 m (false,true,true)+mass3 m (false,false,true) -> Admissions.conditional_A_given_B (stratum_bc_a_no m H)=mass3 m (false,true,true)/(mass3 m (false,true,true)+mass3 m (false,false,true)).
Proof.
  intros m H Hcolumn.
    unfold stratum_bc_a_no.
    apply normalized_four_first_given_second; exact Hcolumn.
Qed.

(**
 [stratum_bc_a_no_odds_ratio] (theorem) — The normalized BC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Mathematical meaning: The normalized BC odds ratio within this selection stratum agrees exactly with the raw selected concordant/discordant cross-product ratio.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), 0<mass3 m (false,true,false)*mass3 m (false,false,true) -> Admissions.admission_odds_ratio (stratum_bc_a_no m H)=(mass3 m (false,true,true)*mass3 m (false,false,false))/(mass3 m (false,true,false)*mass3 m (false,false,true)).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_odds_ratio :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), 0<mass3 m (false,true,false)*mass3 m (false,false,true) -> Admissions.admission_odds_ratio (stratum_bc_a_no m H)=(mass3 m (false,true,true)*mass3 m (false,false,false))/(mass3 m (false,true,false)*mass3 m (false,false,true)).
Proof.
  intros m H Hxy.
    unfold stratum_bc_a_no.
    apply normalized_four_odds_ratio_raw; exact Hxy.
Qed.

(**
 [stratum_bc_a_no_frechet_lower] (theorem) — Conditional overlap in the A-failure stratum satisfies the Fréchet lower bound for the projected BC pair.
 Mathematical meaning: Conditional overlap in the A-failure stratum satisfies the Fréchet lower bound for the projected BC pair.
 Exact checked proposition: forall (m:ThreeTestModel) (H:0<1-pA3 m), Admissions.p_A (stratum_bc_a_no m H)+Admissions.p_B (stratum_bc_a_no m H)-1<=Admissions.p_both (stratum_bc_a_no m H).
 Premises and side conditions: The eight nonnegative atom masses sum to
 one by ThreeTestModel. Conditioning is performed only on a positive-mass
 third-route stratum (pass or fail, as specified). Conditional admission
 ratios and odds add explicit positive row/column and discordant-product
 hypotheses before division.
 Proof/definition method: Reuse the general kernel-checked normalized
 four-cell stratum identities and Admissions two-event bounds; the
 ThreeTestAdmissions finite eight-cell lemmas identify selection mass
 with the appropriate raw-cell total. No ad hoc probability operations,
 unproved stochastic independence or empirical estimates are introduced.
 Library reuse: Admissions.TwoEventModel and conditional/odds/Fréchet
 lemmas; normalized_four_stratum; ThreeTestAdmissions.triple_lra;
 the existing FiniteUnion/FiniteSum canonical event engine; Stdlib tactics.
 Boundary: Exact finite Boolean-event conditional association only; no
 Gaussian conditional law, continuous tail integral or IQ calibration.
*)
Theorem stratum_bc_a_no_frechet_lower :
  forall (m:ThreeTestModel) (H:0<1-pA3 m), Admissions.p_A (stratum_bc_a_no m H)+Admissions.p_B (stratum_bc_a_no m H)-1<=Admissions.p_both (stratum_bc_a_no m H).
Proof.
  intros m H.
    apply Admissions.frechet_lower_bound.
Qed.

(**
 [simpson_reversal_weight] (definition) — An exact, strictly positive eight-atom probability table whose two C-strata each have negative AB association while the pooled AB pair has positive association.
 Mathematical meaning: An exact, strictly positive eight-atom probability table whose two C-strata each have negative AB association while the pooled AB pair has positive association.
 Exact declaration: Definition simpson_reversal_weight (t:triple_outcome):R; eight explicitly rational cell values.
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Use the canonical three-Boolean event projections and an exhaustive match; no custom sum recursion.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Definition simpson_reversal_weight (t:triple_outcome) : R :=
  match (testA3 t,testB3 t,testC3 t) with
  | (true,true,true) => 63/200
  | (true,true,false) => 3/200
  | (true,false,true) => 17/200
  | (true,false,false) => 17/200
  | (false,true,true) => 17/200
  | (false,true,false) => 17/200
  | (false,false,true) => 3/200
  | (false,false,false) => 63/200
  end.

(**
 [simpson_reversal_model] (definition) — The exhaustive eight-atom Simpson example is a certified nonnegative, unit-normalized ThreeTestModel.
 Mathematical meaning: The exhaustive eight-atom Simpson example is a certified nonnegative, unit-normalized ThreeTestModel.
 Exact declaration: Definition simpson_reversal_model : ThreeTestModel.
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Prove all eight raw weights are nonnegative by boolean case analysis, and prove exact total mass one by canonical FiniteSum and rational field arithmetic.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Definition simpson_reversal_model : ThreeTestModel.
Proof.
  refine {| mass3 := simpson_reversal_weight |}.
  - intros t.
    destruct t as [u v].
    destruct u; destruct v;
      repeat match goal with b:bool |- _ => destruct b end.
    all: (cbv [simpson_reversal_weight testA3 testB3 testC3];
          unfold Rdiv;
          apply Rmult_le_pos;
          [lra | apply Rlt_le, Rinv_0_lt_compat; lra]).
  - cbv [FiniteSum.finite_sum triple_cases simpson_reversal_weight
         testA3 testB3 testC3 List.map List.fold_right].
    field; lra.
Defined.

(* The same centralized finite-event unfolding is used to certify the
   example's exact marginal and overlap values; this tactic introduces
   no axioms or independent probability accumulation method. *)
Ltac simpson_exact :=
  cbv [pA3 pB3 pC3 pAB3 triple_prob simpson_reversal_model
       simpson_reversal_weight
       FiniteUnion.finite_prob FiniteUnion.indicator
       FiniteUnion.finite_sum FiniteSum.finite_sum triple_cases
       testA3 testB3 testC3 List.map List.fold_right];
  field; lra.

(**
 [simpson_A_half] (theorem) — The pooled first-route admission marginal of the certified example equals one-half.
 Mathematical meaning: The pooled first-route admission marginal of the certified example equals one-half.
 Exact checked proposition: pA3 simpson_reversal_model = 1/2
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_A_half :
  pA3 simpson_reversal_model = 1/2.
Proof.
  simpson_exact.
Qed.

(**
 [simpson_B_half] (theorem) — The pooled second-route admission marginal of the certified example equals one-half.
 Mathematical meaning: The pooled second-route admission marginal of the certified example equals one-half.
 Exact checked proposition: pB3 simpson_reversal_model = 1/2
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_B_half :
  pB3 simpson_reversal_model = 1/2.
Proof.
  simpson_exact.
Qed.

(**
 [simpson_C_half] (theorem) — The selection-stratum probability is one-half for each C value.
 Mathematical meaning: The selection-stratum probability is one-half for each C value.
 Exact checked proposition: pC3 simpson_reversal_model = 1/2
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_C_half :
  pC3 simpson_reversal_model = 1/2.
Proof.
  simpson_exact.
Qed.

(**
 [simpson_joint_thirty_three_percent] (theorem) — The pooled AB joint success mass is exactly 33%, exceeding the 25% independence product of the marginals.
 Mathematical meaning: The pooled AB joint success mass is exactly 33%, exceeding the 25% independence product of the marginals.
 Exact checked proposition: pAB3 simpson_reversal_model = 33/100
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_joint_thirty_three_percent :
  pAB3 simpson_reversal_model = 33/100.
Proof.
  simpson_exact.
Qed.

(**
 [simpson_pooled_positive_association] (theorem) — The pooled AB binary indicator covariance is strictly positive despite negative conditional dependence inside each C stratum.
 Mathematical meaning: The pooled AB binary indicator covariance is strictly positive despite negative conditional dependence inside each C stratum.
 Exact checked proposition: pA3 simpson_reversal_model*pB3 simpson_reversal_model < pAB3 simpson_reversal_model
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_pooled_positive_association :
  pA3 simpson_reversal_model*pB3 simpson_reversal_model < pAB3 simpson_reversal_model.
Proof.
  rewrite simpson_A_half, simpson_B_half, simpson_joint_thirty_three_percent; nra.
Qed.

(**
 [simpson_C_pass_positive_probability] (theorem) — The C-pass stratum has strictly positive probability, ensuring its conditional two-event model is well-defined.
 Mathematical meaning: The C-pass stratum has strictly positive probability, ensuring its conditional two-event model is well-defined.
 Exact checked proposition: 0 < pC3 simpson_reversal_model
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_C_pass_positive_probability :
  0 < pC3 simpson_reversal_model.
Proof.
  rewrite simpson_C_half; lra.
Qed.

(**
 [simpson_C_fail_positive_probability] (theorem) — The C-fail stratum has strictly positive probability, ensuring its conditional two-event model is well-defined.
 Mathematical meaning: The C-fail stratum has strictly positive probability, ensuring its conditional two-event model is well-defined.
 Exact checked proposition: 0 < 1-pC3 simpson_reversal_model
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_C_fail_positive_probability :
  0 < 1-pC3 simpson_reversal_model.
Proof.
  rewrite simpson_C_half; lra.
Qed.

(**
 [simpson_AB_negative_given_C_pass] (theorem) — Within C passers, A and B have negative conditional binary-indicator association.
 Mathematical meaning: Within C passers, A and B have negative conditional binary-indicator association.
 Exact checked proposition: forall (H:0<pC3 simpson_reversal_model), Admissions.admission_association (stratum_ab_c_yes simpson_reversal_model H) < 0
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_AB_negative_given_C_pass :
  forall (H:0<pC3 simpson_reversal_model), Admissions.admission_association (stratum_ab_c_yes simpson_reversal_model H) < 0.
Proof.
  intro H.
  apply (proj2 (stratum_ab_c_yes_association_negative_iff_raw simpson_reversal_model H)).
  change ((63/200)*(3/200)<(17/200)*(17/200)).
  nra.
Qed.

(**
 [simpson_AB_negative_given_C_fail] (theorem) — Within C nonpassers, A and B also have negative conditional binary-indicator association.
 Mathematical meaning: Within C nonpassers, A and B also have negative conditional binary-indicator association.
 Exact checked proposition: forall (H:0<1-pC3 simpson_reversal_model), Admissions.admission_association (stratum_ab_c_no simpson_reversal_model H) < 0
 Premises and side conditions: All eight Boolean admission-pattern masses
 are explicitly enumerated. The concrete example has equal-mass conditioning
 strata and nonnegative weights summing exactly to one. Its conditional
 association statements only use positive-mass strata and the separately
 verified normalized four-cell projections; no independence is assumed.
 Proof/definition method: Simplify the finite Boolean enumeration to exact rational real arithmetic and reuse the already checked conditional-independence/association bridge.
 Library reuse: ThreeTestAdmissions finite probability and eight-outcome
 model, the canonical FiniteUnion/FiniteSum engine, Admissions association
 criteria, normalized_four_stratum, and Stdlib.Lra/Psatz/Field.
 Boundary: This example demonstrates selection-induced sign reversal in
 finite probability alone. It is not evidence about observed IQ, institutions,
 normal tails or a Gaussian conditional distribution.
*)
Theorem simpson_AB_negative_given_C_fail :
  forall (H:0<1-pC3 simpson_reversal_model), Admissions.admission_association (stratum_ab_c_no simpson_reversal_model H) < 0.
Proof.
  intro H.
  apply (proj2 (stratum_ab_c_no_association_negative_iff_raw simpson_reversal_model H)).
  change ((3/200)*(63/200)<(17/200)*(17/200)).
  nra.
Qed.

