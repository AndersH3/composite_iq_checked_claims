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

