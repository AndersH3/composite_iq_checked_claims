(** Module: ThreeTestPairBridge.v
  Purpose: Embed the three-test admissions report's exact eight-outcome
  model into three checked two-test models and inherit pairwise conditional
  probability, association, Fréchet and correlation/odds controls.
  Mathematical representation: For each pair AB, AC and BC, sum disjoint
  atomic masses over the omitted third decision to obtain four nonnegative
  contingency cells. Each certified Admissions.TwoEventModel retains unit
  mass by the existing ThreeTestModel normalization invariant.
  Explicit hypotheses: All atomic weights are nonnegative and unit
  normalized. Probability-ratio interpretations require strictly positive
  conditioning marginals; odds/phi results state denominator premises.
  Library use: ThreeTestAdmissions' shared FiniteUnion/FiniteSum probability
  implementation; the fully proven Admissions two-event conditional,
  binary-independence, association, phi and odds-ratio library;
  Rocq Stdlib.Reals, Lra, Psatz and Ring. No new probability sums or matrices.
  Limitations: These results apply to discrete Boolean admissions events.
  They do not establish any Gaussian conditioning, trivariate normal tail,
  psychometric correlation, or actual institution admissions probability.
  Reproduction: scripts/compile_rocq.sh with pinned Rocq Prover 9.2,
  compiling after ThreeTestAdmissions.v and its shared dependencies.
  AI disclosure: OpenAI ChatGPT generated the math proof statements,
  constructions and documentation; only the pinned Rocq kernel validates
  formal proof objects at the recorded source commit.
*)
From Stdlib Require Import Reals Lra Psatz.
Require Import Admissions ThreeTestAdmissions.
Open Scope R_scope.

(**
 [pair_AB3] (definition) — Forgetting the unused Boolean test leaves a normalized two-test A/B contingency distribution, with exact joint/first-only/second-only/neither cells.
 Mathematical meaning: Forgetting the unused Boolean test leaves a normalized two-test A/B contingency distribution, with exact joint/first-only/second-only/neither cells.
 Exact declaration: forall m : ThreeTestModel, pair_AB3 m : Admissions.TwoEventModel
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Construct the four disjoint marginal cell masses and close all record validity obligations using the normalized eight-outcome mass proof.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Definition pair_AB3 (m : ThreeTestModel) : Admissions.TwoEventModel.
Proof.
  refine {| Admissions.joint := mass3 m (true,true,true) + mass3 m (true,true,false);
            Admissions.only_A := mass3 m (true,false,true) + mass3 m (true,false,false);
            Admissions.only_B := mass3 m (false,true,true) + mass3 m (false,true,false);
            Admissions.neither := mass3 m (false,false,true) + mass3 m (false,false,false) |};
    triple_lra.
Defined.

(**
 [triple_ab_joint_mass] (theorem) — The A-B marginal overlap equals its original three-test event mass.
 Mathematical meaning: The A-B marginal overlap equals its original three-test event mass.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_both (pair_AB3 m) = pAB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_joint_mass :
  forall m : ThreeTestModel, Admissions.p_both (pair_AB3 m) = pAB3 m..
Proof.
  intros m;
  unfold Admissions.p_both, pair_AB3; simpl; triple_lra.
Qed.

(**
 [triple_ab_first_only_mass] (theorem) — Exactly A without B is the first marginal minus the pair intersection.
 Mathematical meaning: Exactly A without B is the first marginal minus the pair intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.only_A (pair_AB3 m) = pA3 m-pAB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_first_only_mass :
  forall m : ThreeTestModel, Admissions.only_A (pair_AB3 m) = pA3 m-pAB3 m..
Proof.
  intros m;
  unfold pair_AB3; simpl; triple_lra.
Qed.

(**
 [triple_ab_second_only_mass] (theorem) — Exactly B without A is the second marginal minus the pair intersection.
 Mathematical meaning: Exactly B without A is the second marginal minus the pair intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.only_B (pair_AB3 m) = pB3 m-pAB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_second_only_mass :
  forall m : ThreeTestModel, Admissions.only_B (pair_AB3 m) = pB3 m-pAB3 m..
Proof.
  intros m;
  unfold pair_AB3; simpl; triple_lra.
Qed.

(**
 [triple_ab_neither_mass] (theorem) — Neither A nor B is the complement of their union even when the omitted test succeeds.
 Mathematical meaning: Neither A nor B is the complement of their union even when the omitted test succeeds.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.neither (pair_AB3 m) = 1-(pA3 m+pB3 m-pAB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_neither_mass :
  forall m : ThreeTestModel, Admissions.neither (pair_AB3 m) = 1-(pA3 m+pB3 m-pAB3 m)..
Proof.
  intros m;
  unfold pair_AB3; simpl; triple_lra.
Qed.

(**
 [triple_ab_first_marginal] (theorem) — The certified two-test first-route marginal is exactly the A marginal in the full three-test model.
 Mathematical meaning: The certified two-test first-route marginal is exactly the A marginal in the full three-test model.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_A (pair_AB3 m) = pA3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_first_marginal :
  forall m : ThreeTestModel, Admissions.p_A (pair_AB3 m) = pA3 m..
Proof.
  intros m;
  unfold Admissions.p_A.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_first_only_mass.
  ring.
Qed.

(**
 [triple_ab_second_marginal] (theorem) — The certified two-test second-route marginal is exactly the B marginal in the full three-test model.
 Mathematical meaning: The certified two-test second-route marginal is exactly the B marginal in the full three-test model.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_B (pair_AB3 m) = pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_second_marginal :
  forall m : ThreeTestModel, Admissions.p_B (pair_AB3 m) = pB3 m..
Proof.
  intros m;
  unfold Admissions.p_B.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_second_only_mass.
  ring.
Qed.

(**
 [triple_ab_union_mass] (theorem) — The union of A and B is the sum of its marginals less their intersection.
 Mathematical meaning: The union of A and B is the sum of its marginals less their intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_either (pair_AB3 m) = pA3 m+pB3 m-pAB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_union_mass :
  forall m : ThreeTestModel, Admissions.p_either (pair_AB3 m) = pA3 m+pB3 m-pAB3 m..
Proof.
  intros m;
  unfold Admissions.p_either.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_first_only_mass.
  rewrite triple_ab_second_only_mass.
  ring.
Qed.

(**
 [triple_ab_exclusive_mass] (theorem) — Exactly one of A or B succeeds with two-test mass p_first+p_second−2p_overlap.
 Mathematical meaning: Exactly one of A or B succeeds with two-test mass p_first+p_second−2p_overlap.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_exactly_one (pair_AB3 m) = pA3 m+pB3 m-2*pAB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_exclusive_mass :
  forall m : ThreeTestModel, Admissions.p_exactly_one (pair_AB3 m) = pA3 m+pB3 m-2*pAB3 m..
Proof.
  intros m;
  unfold Admissions.p_exactly_one.
  rewrite triple_ab_first_only_mass.
  rewrite triple_ab_second_only_mass.
  ring.
Qed.

(**
 [triple_ab_conditional_second_given_first] (theorem) — The original B given A admission rate is the projected two-event conditional probability.
 Mathematical meaning: The original B given A admission rate is the projected two-event conditional probability.
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m -> Admissions.conditional_B_given_A (pair_AB3 m) = pAB3 m/pA3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_conditional_second_given_first :
  forall m : ThreeTestModel, 0<pA3 m -> Admissions.conditional_B_given_A (pair_AB3 m) = pAB3 m/pA3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_B_given_A.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_first_marginal.
  reflexivity.
Qed.

(**
 [triple_ab_conditional_first_given_second] (theorem) — The A given B admission rate agrees with the projected two-event conditional.
 Mathematical meaning: The A given B admission rate agrees with the projected two-event conditional.
 Exact checked proposition: forall m : ThreeTestModel, 0<pB3 m -> Admissions.conditional_A_given_B (pair_AB3 m) = pAB3 m/pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_conditional_first_given_second :
  forall m : ThreeTestModel, 0<pB3 m -> Admissions.conditional_A_given_B (pair_AB3 m) = pAB3 m/pB3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_A_given_B.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ab_conditional_overlap_given_union] (theorem) — The chance of admission by both A and B, conditional on at least one, has the exact overlap/union ratio.
 Mathematical meaning: The chance of admission by both A and B, conditional on at least one, has the exact overlap/union ratio.
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m+pB3 m-pAB3 m -> Admissions.conditional_both_given_either (pair_AB3 m) = pAB3 m/(pA3 m+pB3 m-pAB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_conditional_overlap_given_union :
  forall m : ThreeTestModel, 0<pA3 m+pB3 m-pAB3 m -> Admissions.conditional_both_given_either (pair_AB3 m) = pAB3 m/(pA3 m+pB3 m-pAB3 m)..
Proof.
  intros m _.
  unfold Admissions.conditional_both_given_either.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_union_mass.
  reflexivity.
Qed.

(**
 [triple_ab_conditional_notfirst_given_second] (theorem) — Among B passers, the A rejection fraction is the second-only cell divided by its second marginal.
 Mathematical meaning: Among B passers, the A rejection fraction is the second-only cell divided by its second marginal.
 Exact checked proposition: forall m : ThreeTestModel, 0<pB3 m -> Admissions.conditional_not_A_given_B (pair_AB3 m) = (pB3 m-pAB3 m)/pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_conditional_notfirst_given_second :
  forall m : ThreeTestModel, 0<pB3 m -> Admissions.conditional_not_A_given_B (pair_AB3 m) = (pB3 m-pAB3 m)/pB3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_not_A_given_B.
  rewrite triple_ab_second_only_mass.
  rewrite triple_ab_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ab_conditional_second_given_notfirst] (theorem) — Among those not admitted by A, the chance of B admission has a complement-stratum denominator.
 Mathematical meaning: Among those not admitted by A, the chance of B admission has a complement-stratum denominator.
 Exact checked proposition: forall m : ThreeTestModel, 0<1-pA3 m -> Admissions.admission_B_given_not_A (pair_AB3 m) = (pB3 m-pAB3 m)/(1-pA3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_conditional_second_given_notfirst :
  forall m : ThreeTestModel, 0<1-pA3 m -> Admissions.admission_B_given_not_A (pair_AB3 m) = (pB3 m-pAB3 m)/(1-pA3 m)..
Proof.
  intros m _.
  unfold Admissions.admission_B_given_not_A, Admissions.admission_not_A_mass.
  rewrite triple_ab_second_only_mass.
  rewrite triple_ab_neither_mass.
  replace ((pB3 m-pAB3 m)+(1-(pA3 m+pB3 m-pAB3 m))) with (1-pA3 m) by ring.
  reflexivity.
Qed.

(**
 [triple_ab_conditional_first_given_notsecond] (theorem) — Among those not admitted by B, the chance of A admission uses the other complement stratum.
 Mathematical meaning: Among those not admitted by B, the chance of A admission uses the other complement stratum.
 Exact checked proposition: forall m : ThreeTestModel, 0<1-pB3 m -> Admissions.admission_A_given_not_B (pair_AB3 m) = (pA3 m-pAB3 m)/(1-pB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_conditional_first_given_notsecond :
  forall m : ThreeTestModel, 0<1-pB3 m -> Admissions.admission_A_given_not_B (pair_AB3 m) = (pA3 m-pAB3 m)/(1-pB3 m)..
Proof.
  intros m _.
  unfold Admissions.admission_A_given_not_B, Admissions.admission_not_B_mass.
  rewrite triple_ab_first_only_mass.
  rewrite triple_ab_neither_mass.
  replace ((pA3 m-pAB3 m)+(1-(pA3 m+pB3 m-pAB3 m))) with (1-pB3 m) by ring.
  reflexivity.
Qed.

(**
 [triple_ab_association_covariance] (theorem) — The A/B 2×2 cross-product association is exactly joint probability minus the product of marginals.
 Mathematical meaning: The A/B 2×2 cross-product association is exactly joint probability minus the product of marginals.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_AB3 m) = pAB3 m-pA3 m*pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_association_covariance :
  forall m : ThreeTestModel, Admissions.admission_association (pair_AB3 m) = pAB3 m-pA3 m*pB3 m..
Proof.
  intro m.
  rewrite Admissions.admission_association_covariance.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_first_marginal.
  rewrite triple_ab_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ab_independence_criterion] (theorem) — Independence of A and B in the three-route population is equivalent to a vanishing projected contingency association.
 Mathematical meaning: Independence of A and B in the three-route population is equivalent to a vanishing projected contingency association.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_AB3 m)=0 <-> pAB3 m=pA3 m*pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_independence_criterion :
  forall m : ThreeTestModel, Admissions.admission_association (pair_AB3 m)=0 <-> pAB3 m=pA3 m*pB3 m..
Proof.
  intros m.
  rewrite (Admissions.admission_association_zero_iff_independence (pair_AB3 m)).
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_first_marginal.
  rewrite triple_ab_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ab_union_independent_reference] (theorem) — The independent-reference union estimate differs from the actual A/B union by exactly the admission association.
 Mathematical meaning: The independent-reference union estimate differs from the actual A/B union by exactly the admission association.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pB3 m-pAB3 m = pA3 m+pB3 m-pA3 m*pB3 m-Admissions.admission_association (pair_AB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_union_independent_reference :
  forall m : ThreeTestModel, pA3 m+pB3 m-pAB3 m = pA3 m+pB3 m-pA3 m*pB3 m-Admissions.admission_association (pair_AB3 m)..
Proof.
  intro m.
  rewrite triple_ab_association_covariance.
  ring.
Qed.

(**
 [triple_ab_first_indicator_variance] (theorem) — The Bernoulli success variance of route A in the two-route projection matches its full-model marginal.
 Mathematical meaning: The Bernoulli success variance of route A in the two-route projection matches its full-model marginal.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_indicator_variance_A (pair_AB3 m) = pA3 m*(1-pA3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_first_indicator_variance :
  forall m : ThreeTestModel, Admissions.admission_indicator_variance_A (pair_AB3 m) = pA3 m*(1-pA3 m)..
Proof.
  intro m.
  unfold Admissions.admission_indicator_variance_A.
  rewrite triple_ab_first_marginal.
  reflexivity.
Qed.

(**
 [triple_ab_second_indicator_variance] (theorem) — The Bernoulli success variance of route B in the two-route projection matches its full-model marginal.
 Mathematical meaning: The Bernoulli success variance of route B in the two-route projection matches its full-model marginal.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_indicator_variance_B (pair_AB3 m) = pB3 m*(1-pB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_second_indicator_variance :
  forall m : ThreeTestModel, Admissions.admission_indicator_variance_B (pair_AB3 m) = pB3 m*(1-pB3 m)..
Proof.
  intro m.
  unfold Admissions.admission_indicator_variance_B.
  rewrite triple_ab_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ab_odds_ratio] (theorem) — The A/B odds ratio is the exact concordant/discordant probability cross-product for its marginalized cells.
 Mathematical meaning: The A/B odds ratio is the exact concordant/discordant probability cross-product for its marginalized cells.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_odds_ratio (pair_AB3 m) = pAB3 m*(1-(pA3 m+pB3 m-pAB3 m))/(((pA3 m-pAB3 m)*(pB3 m-pAB3 m))).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_odds_ratio :
  forall m : ThreeTestModel, Admissions.admission_odds_ratio (pair_AB3 m) = pAB3 m*(1-(pA3 m+pB3 m-pAB3 m))/(((pA3 m-pAB3 m)*(pB3 m-pAB3 m)))..
Proof.
  intro m.
  unfold Admissions.admission_odds_ratio.
  rewrite triple_ab_joint_mass.
  rewrite triple_ab_neither_mass.
  rewrite triple_ab_first_only_mass.
  rewrite triple_ab_second_only_mass.
  reflexivity.
Qed.

(**
 [triple_ab_phi_coefficient] (theorem) — The projected A/B phi coefficient equals the standardized joint-minus-product association with its own Bernoulli variances.
 Mathematical meaning: The projected A/B phi coefficient equals the standardized joint-minus-product association with its own Bernoulli variances.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_phi (pair_AB3 m) = (pAB3 m-pA3 m*pB3 m)/sqrt ((pA3 m*(1-pA3 m))*(pB3 m*(1-pB3 m))).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_phi_coefficient :
  forall m : ThreeTestModel, Admissions.admission_phi (pair_AB3 m) = (pAB3 m-pA3 m*pB3 m)/sqrt ((pA3 m*(1-pA3 m))*(pB3 m*(1-pB3 m)))..
Proof.
  intro m.
  unfold Admissions.admission_phi.
  rewrite triple_ab_association_covariance.
  rewrite triple_ab_first_indicator_variance.
  rewrite triple_ab_second_indicator_variance.
  reflexivity.
Qed.

(**
 [triple_ab_frechet_lower_bound] (theorem) — The full three-test model obeys the sharp pairwise A/B Fréchet lower overlap bound without assuming independence.
 Mathematical meaning: The full three-test model obeys the sharp pairwise A/B Fréchet lower overlap bound without assuming independence.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pB3 m-1<=pAB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_frechet_lower_bound :
  forall m : ThreeTestModel, pA3 m+pB3 m-1<=pAB3 m..
Proof.
  intro m.
  pose proof (Admissions.frechet_lower_bound (pair_AB3 m)) as H.
  rewrite triple_ab_first_marginal, triple_ab_second_marginal,
          triple_ab_joint_mass in H.
  exact H.
Qed.

(**
 [triple_ab_conditional_second_interval] (theorem) — Conditional B admission among A passers is a probability in [0,1] whenever the conditioning marginal is positive.
 Mathematical meaning: Conditional B admission among A passers is a probability in [0,1] whenever the conditioning marginal is positive.
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m -> 0<=Admissions.conditional_B_given_A (pair_AB3 m) /\ Admissions.conditional_B_given_A (pair_AB3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_conditional_second_interval :
  forall m : ThreeTestModel, 0<pA3 m -> 0<=Admissions.conditional_B_given_A (pair_AB3 m) /\ Admissions.conditional_B_given_A (pair_AB3 m)<=1..
Proof.
  intros m Hx.
  apply Admissions.conditional_B_given_A_unit_interval.
  rewrite triple_ab_first_marginal; exact Hx.
Qed.

(**
 [triple_ab_association_positive_iff] (theorem) — Positive A/B association is exactly strict positive excess overlap above the independent-product reference.
 Mathematical meaning: Positive A/B association is exactly strict positive excess overlap above the independent-product reference.
 Exact checked proposition: forall m : ThreeTestModel, 0<Admissions.admission_association (pair_AB3 m) <-> pA3 m*pB3 m<pAB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_association_positive_iff :
  forall m : ThreeTestModel, 0<Admissions.admission_association (pair_AB3 m) <-> pA3 m*pB3 m<pAB3 m..
Proof.
  intro m.
  rewrite (Admissions.admission_association_positive_iff_overlap (pair_AB3 m)).
  rewrite triple_ab_first_marginal.
  rewrite triple_ab_second_marginal.
  rewrite triple_ab_joint_mass.
  reflexivity.
Qed.

(**
 [triple_ab_association_negative_iff] (theorem) — Negative A/B association is exactly strict overlap below the independent-product reference.
 Mathematical meaning: Negative A/B association is exactly strict overlap below the independent-product reference.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_AB3 m)<0 <-> pAB3 m<pA3 m*pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_association_negative_iff :
  forall m : ThreeTestModel, Admissions.admission_association (pair_AB3 m)<0 <-> pAB3 m<pA3 m*pB3 m..
Proof.
  intro m.
  rewrite (Admissions.admission_association_negative_iff_overlap (pair_AB3 m)).
  rewrite triple_ab_first_marginal.
  rewrite triple_ab_second_marginal.
  rewrite triple_ab_joint_mass.
  reflexivity.
Qed.

(**
 [triple_ab_odds_one_iff_independent] (theorem) — When both discordant cells have positive product, the A/B odds ratio is one exactly at pairwise independence.
 Mathematical meaning: When both discordant cells have positive product, the A/B odds ratio is one exactly at pairwise independence.
 Exact checked proposition: forall m : ThreeTestModel, 0<Admissions.only_A (pair_AB3 m)*Admissions.only_B (pair_AB3 m) -> (Admissions.admission_odds_ratio (pair_AB3 m)=1 <-> pAB3 m=pA3 m*pB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_odds_one_iff_independent :
  forall m : ThreeTestModel, 0<Admissions.only_A (pair_AB3 m)*Admissions.only_B (pair_AB3 m) -> (Admissions.admission_odds_ratio (pair_AB3 m)=1 <-> pAB3 m=pA3 m*pB3 m)..
Proof.
  intros m Hpos.
  pose proof (Admissions.admission_odds_ratio_one_iff_independent (pair_AB3 m) Hpos) as H.
  rewrite triple_ab_joint_mass, triple_ab_first_marginal,
          triple_ab_second_marginal in H.
  exact H.
Qed.

(**
 [triple_ab_phi_unit_interval] (theorem) — With strictly positive Bernoulli variances, projected A/B phi correlation lies in [-1,1].
 Mathematical meaning: With strictly positive Bernoulli variances, projected A/B phi correlation lies in [-1,1].
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m -> pA3 m<1 -> 0<pB3 m -> pB3 m<1 -> -1<=Admissions.admission_phi (pair_AB3 m) /\ Admissions.admission_phi (pair_AB3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_phi_unit_interval :
  forall m : ThreeTestModel, 0<pA3 m -> pA3 m<1 -> 0<pB3 m -> pB3 m<1 -> -1<=Admissions.admission_phi (pair_AB3 m) /\ Admissions.admission_phi (pair_AB3 m)<=1..
Proof.
  intros m Hx0 Hx1 Hy0 Hy1.
  apply Admissions.admission_phi_unit_interval;
  (rewrite triple_ab_first_marginal || rewrite triple_ab_second_marginal); assumption.
Qed.

(**
 [triple_ab_union_unit_interval] (theorem) — The projection of A/B admissions has a normalized nonnegative union probability at most one.
 Mathematical meaning: The projection of A/B admissions has a normalized nonnegative union probability at most one.
 Exact checked proposition: forall m : ThreeTestModel, 0<=Admissions.p_either (pair_AB3 m) /\ Admissions.p_either (pair_AB3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ab_union_unit_interval :
  forall m : ThreeTestModel, 0<=Admissions.p_either (pair_AB3 m) /\ Admissions.p_either (pair_AB3 m)<=1..
Proof.
  intro m; split.
  - apply Admissions.union_nonnegative.
  - apply Admissions.union_at_most_one.
Qed.

(**
 [pair_AC3] (definition) — Forgetting the unused Boolean test leaves a normalized two-test A/C contingency distribution, with exact joint/first-only/second-only/neither cells.
 Mathematical meaning: Forgetting the unused Boolean test leaves a normalized two-test A/C contingency distribution, with exact joint/first-only/second-only/neither cells.
 Exact declaration: forall m : ThreeTestModel, pair_AC3 m : Admissions.TwoEventModel
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Construct the four disjoint marginal cell masses and close all record validity obligations using the normalized eight-outcome mass proof.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Definition pair_AC3 (m : ThreeTestModel) : Admissions.TwoEventModel.
Proof.
  refine {| Admissions.joint := mass3 m (true,true,true) + mass3 m (true,false,true);
            Admissions.only_A := mass3 m (true,true,false) + mass3 m (true,false,false);
            Admissions.only_B := mass3 m (false,true,true) + mass3 m (false,false,true);
            Admissions.neither := mass3 m (false,true,false) + mass3 m (false,false,false) |};
    triple_lra.
Defined.

(**
 [triple_ac_joint_mass] (theorem) — The A-C marginal overlap equals its original three-test event mass.
 Mathematical meaning: The A-C marginal overlap equals its original three-test event mass.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_both (pair_AC3 m) = pAC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_joint_mass :
  forall m : ThreeTestModel, Admissions.p_both (pair_AC3 m) = pAC3 m..
Proof.
  intros m;
  unfold Admissions.p_both, pair_AC3; simpl; triple_lra.
Qed.

(**
 [triple_ac_first_only_mass] (theorem) — Exactly A without C is the first marginal minus the pair intersection.
 Mathematical meaning: Exactly A without C is the first marginal minus the pair intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.only_A (pair_AC3 m) = pA3 m-pAC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_first_only_mass :
  forall m : ThreeTestModel, Admissions.only_A (pair_AC3 m) = pA3 m-pAC3 m..
Proof.
  intros m;
  unfold pair_AC3; simpl; triple_lra.
Qed.

(**
 [triple_ac_second_only_mass] (theorem) — Exactly C without A is the second marginal minus the pair intersection.
 Mathematical meaning: Exactly C without A is the second marginal minus the pair intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.only_B (pair_AC3 m) = pC3 m-pAC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_second_only_mass :
  forall m : ThreeTestModel, Admissions.only_B (pair_AC3 m) = pC3 m-pAC3 m..
Proof.
  intros m;
  unfold pair_AC3; simpl; triple_lra.
Qed.

(**
 [triple_ac_neither_mass] (theorem) — Neither A nor C is the complement of their union even when the omitted test succeeds.
 Mathematical meaning: Neither A nor C is the complement of their union even when the omitted test succeeds.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.neither (pair_AC3 m) = 1-(pA3 m+pC3 m-pAC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_neither_mass :
  forall m : ThreeTestModel, Admissions.neither (pair_AC3 m) = 1-(pA3 m+pC3 m-pAC3 m)..
Proof.
  intros m;
  unfold pair_AC3; simpl; triple_lra.
Qed.

(**
 [triple_ac_first_marginal] (theorem) — The certified two-test first-route marginal is exactly the A marginal in the full three-test model.
 Mathematical meaning: The certified two-test first-route marginal is exactly the A marginal in the full three-test model.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_A (pair_AC3 m) = pA3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_first_marginal :
  forall m : ThreeTestModel, Admissions.p_A (pair_AC3 m) = pA3 m..
Proof.
  intros m;
  unfold Admissions.p_A.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_first_only_mass.
  ring.
Qed.

(**
 [triple_ac_second_marginal] (theorem) — The certified two-test second-route marginal is exactly the C marginal in the full three-test model.
 Mathematical meaning: The certified two-test second-route marginal is exactly the C marginal in the full three-test model.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_B (pair_AC3 m) = pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_second_marginal :
  forall m : ThreeTestModel, Admissions.p_B (pair_AC3 m) = pC3 m..
Proof.
  intros m;
  unfold Admissions.p_B.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_second_only_mass.
  ring.
Qed.

(**
 [triple_ac_union_mass] (theorem) — The union of A and C is the sum of its marginals less their intersection.
 Mathematical meaning: The union of A and C is the sum of its marginals less their intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_either (pair_AC3 m) = pA3 m+pC3 m-pAC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_union_mass :
  forall m : ThreeTestModel, Admissions.p_either (pair_AC3 m) = pA3 m+pC3 m-pAC3 m..
Proof.
  intros m;
  unfold Admissions.p_either.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_first_only_mass.
  rewrite triple_ac_second_only_mass.
  ring.
Qed.

(**
 [triple_ac_exclusive_mass] (theorem) — Exactly one of A or C succeeds with two-test mass p_first+p_second−2p_overlap.
 Mathematical meaning: Exactly one of A or C succeeds with two-test mass p_first+p_second−2p_overlap.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_exactly_one (pair_AC3 m) = pA3 m+pC3 m-2*pAC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_exclusive_mass :
  forall m : ThreeTestModel, Admissions.p_exactly_one (pair_AC3 m) = pA3 m+pC3 m-2*pAC3 m..
Proof.
  intros m;
  unfold Admissions.p_exactly_one.
  rewrite triple_ac_first_only_mass.
  rewrite triple_ac_second_only_mass.
  ring.
Qed.

(**
 [triple_ac_conditional_second_given_first] (theorem) — The original C given A admission rate is the projected two-event conditional probability.
 Mathematical meaning: The original C given A admission rate is the projected two-event conditional probability.
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m -> Admissions.conditional_B_given_A (pair_AC3 m) = pAC3 m/pA3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_conditional_second_given_first :
  forall m : ThreeTestModel, 0<pA3 m -> Admissions.conditional_B_given_A (pair_AC3 m) = pAC3 m/pA3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_B_given_A.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_first_marginal.
  reflexivity.
Qed.

(**
 [triple_ac_conditional_first_given_second] (theorem) — The A given C admission rate agrees with the projected two-event conditional.
 Mathematical meaning: The A given C admission rate agrees with the projected two-event conditional.
 Exact checked proposition: forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_A_given_B (pair_AC3 m) = pAC3 m/pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_conditional_first_given_second :
  forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_A_given_B (pair_AC3 m) = pAC3 m/pC3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_A_given_B.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ac_conditional_overlap_given_union] (theorem) — The chance of admission by both A and C, conditional on at least one, has the exact overlap/union ratio.
 Mathematical meaning: The chance of admission by both A and C, conditional on at least one, has the exact overlap/union ratio.
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m+pC3 m-pAC3 m -> Admissions.conditional_both_given_either (pair_AC3 m) = pAC3 m/(pA3 m+pC3 m-pAC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_conditional_overlap_given_union :
  forall m : ThreeTestModel, 0<pA3 m+pC3 m-pAC3 m -> Admissions.conditional_both_given_either (pair_AC3 m) = pAC3 m/(pA3 m+pC3 m-pAC3 m)..
Proof.
  intros m _.
  unfold Admissions.conditional_both_given_either.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_union_mass.
  reflexivity.
Qed.

(**
 [triple_ac_conditional_notfirst_given_second] (theorem) — Among C passers, the A rejection fraction is the second-only cell divided by its second marginal.
 Mathematical meaning: Among C passers, the A rejection fraction is the second-only cell divided by its second marginal.
 Exact checked proposition: forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_not_A_given_B (pair_AC3 m) = (pC3 m-pAC3 m)/pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_conditional_notfirst_given_second :
  forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_not_A_given_B (pair_AC3 m) = (pC3 m-pAC3 m)/pC3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_not_A_given_B.
  rewrite triple_ac_second_only_mass.
  rewrite triple_ac_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ac_conditional_second_given_notfirst] (theorem) — Among those not admitted by A, the chance of C admission has a complement-stratum denominator.
 Mathematical meaning: Among those not admitted by A, the chance of C admission has a complement-stratum denominator.
 Exact checked proposition: forall m : ThreeTestModel, 0<1-pA3 m -> Admissions.admission_B_given_not_A (pair_AC3 m) = (pC3 m-pAC3 m)/(1-pA3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_conditional_second_given_notfirst :
  forall m : ThreeTestModel, 0<1-pA3 m -> Admissions.admission_B_given_not_A (pair_AC3 m) = (pC3 m-pAC3 m)/(1-pA3 m)..
Proof.
  intros m _.
  unfold Admissions.admission_B_given_not_A, Admissions.admission_not_A_mass.
  rewrite triple_ac_second_only_mass.
  rewrite triple_ac_neither_mass.
  replace ((pC3 m-pAC3 m)+(1-(pA3 m+pC3 m-pAC3 m))) with (1-pA3 m) by ring.
  reflexivity.
Qed.

(**
 [triple_ac_conditional_first_given_notsecond] (theorem) — Among those not admitted by C, the chance of A admission uses the other complement stratum.
 Mathematical meaning: Among those not admitted by C, the chance of A admission uses the other complement stratum.
 Exact checked proposition: forall m : ThreeTestModel, 0<1-pC3 m -> Admissions.admission_A_given_not_B (pair_AC3 m) = (pA3 m-pAC3 m)/(1-pC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_conditional_first_given_notsecond :
  forall m : ThreeTestModel, 0<1-pC3 m -> Admissions.admission_A_given_not_B (pair_AC3 m) = (pA3 m-pAC3 m)/(1-pC3 m)..
Proof.
  intros m _.
  unfold Admissions.admission_A_given_not_B, Admissions.admission_not_B_mass.
  rewrite triple_ac_first_only_mass.
  rewrite triple_ac_neither_mass.
  replace ((pA3 m-pAC3 m)+(1-(pA3 m+pC3 m-pAC3 m))) with (1-pC3 m) by ring.
  reflexivity.
Qed.

(**
 [triple_ac_association_covariance] (theorem) — The A/C 2×2 cross-product association is exactly joint probability minus the product of marginals.
 Mathematical meaning: The A/C 2×2 cross-product association is exactly joint probability minus the product of marginals.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_AC3 m) = pAC3 m-pA3 m*pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_association_covariance :
  forall m : ThreeTestModel, Admissions.admission_association (pair_AC3 m) = pAC3 m-pA3 m*pC3 m..
Proof.
  intro m.
  rewrite Admissions.admission_association_covariance.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_first_marginal.
  rewrite triple_ac_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ac_independence_criterion] (theorem) — Independence of A and C in the three-route population is equivalent to a vanishing projected contingency association.
 Mathematical meaning: Independence of A and C in the three-route population is equivalent to a vanishing projected contingency association.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_AC3 m)=0 <-> pAC3 m=pA3 m*pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_independence_criterion :
  forall m : ThreeTestModel, Admissions.admission_association (pair_AC3 m)=0 <-> pAC3 m=pA3 m*pC3 m..
Proof.
  intros m.
  rewrite (Admissions.admission_association_zero_iff_independence (pair_AC3 m)).
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_first_marginal.
  rewrite triple_ac_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ac_union_independent_reference] (theorem) — The independent-reference union estimate differs from the actual A/C union by exactly the admission association.
 Mathematical meaning: The independent-reference union estimate differs from the actual A/C union by exactly the admission association.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pC3 m-pAC3 m = pA3 m+pC3 m-pA3 m*pC3 m-Admissions.admission_association (pair_AC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_union_independent_reference :
  forall m : ThreeTestModel, pA3 m+pC3 m-pAC3 m = pA3 m+pC3 m-pA3 m*pC3 m-Admissions.admission_association (pair_AC3 m)..
Proof.
  intro m.
  rewrite triple_ac_association_covariance.
  ring.
Qed.

(**
 [triple_ac_first_indicator_variance] (theorem) — The Bernoulli success variance of route A in the two-route projection matches its full-model marginal.
 Mathematical meaning: The Bernoulli success variance of route A in the two-route projection matches its full-model marginal.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_indicator_variance_A (pair_AC3 m) = pA3 m*(1-pA3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_first_indicator_variance :
  forall m : ThreeTestModel, Admissions.admission_indicator_variance_A (pair_AC3 m) = pA3 m*(1-pA3 m)..
Proof.
  intro m.
  unfold Admissions.admission_indicator_variance_A.
  rewrite triple_ac_first_marginal.
  reflexivity.
Qed.

(**
 [triple_ac_second_indicator_variance] (theorem) — The Bernoulli success variance of route C in the two-route projection matches its full-model marginal.
 Mathematical meaning: The Bernoulli success variance of route C in the two-route projection matches its full-model marginal.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_indicator_variance_B (pair_AC3 m) = pC3 m*(1-pC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_second_indicator_variance :
  forall m : ThreeTestModel, Admissions.admission_indicator_variance_B (pair_AC3 m) = pC3 m*(1-pC3 m)..
Proof.
  intro m.
  unfold Admissions.admission_indicator_variance_B.
  rewrite triple_ac_second_marginal.
  reflexivity.
Qed.

(**
 [triple_ac_odds_ratio] (theorem) — The A/C odds ratio is the exact concordant/discordant probability cross-product for its marginalized cells.
 Mathematical meaning: The A/C odds ratio is the exact concordant/discordant probability cross-product for its marginalized cells.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_odds_ratio (pair_AC3 m) = pAC3 m*(1-(pA3 m+pC3 m-pAC3 m))/(((pA3 m-pAC3 m)*(pC3 m-pAC3 m))).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_odds_ratio :
  forall m : ThreeTestModel, Admissions.admission_odds_ratio (pair_AC3 m) = pAC3 m*(1-(pA3 m+pC3 m-pAC3 m))/(((pA3 m-pAC3 m)*(pC3 m-pAC3 m)))..
Proof.
  intro m.
  unfold Admissions.admission_odds_ratio.
  rewrite triple_ac_joint_mass.
  rewrite triple_ac_neither_mass.
  rewrite triple_ac_first_only_mass.
  rewrite triple_ac_second_only_mass.
  reflexivity.
Qed.

(**
 [triple_ac_phi_coefficient] (theorem) — The projected A/C phi coefficient equals the standardized joint-minus-product association with its own Bernoulli variances.
 Mathematical meaning: The projected A/C phi coefficient equals the standardized joint-minus-product association with its own Bernoulli variances.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_phi (pair_AC3 m) = (pAC3 m-pA3 m*pC3 m)/sqrt ((pA3 m*(1-pA3 m))*(pC3 m*(1-pC3 m))).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_phi_coefficient :
  forall m : ThreeTestModel, Admissions.admission_phi (pair_AC3 m) = (pAC3 m-pA3 m*pC3 m)/sqrt ((pA3 m*(1-pA3 m))*(pC3 m*(1-pC3 m)))..
Proof.
  intro m.
  unfold Admissions.admission_phi.
  rewrite triple_ac_association_covariance.
  rewrite triple_ac_first_indicator_variance.
  rewrite triple_ac_second_indicator_variance.
  reflexivity.
Qed.

(**
 [triple_ac_frechet_lower_bound] (theorem) — The full three-test model obeys the sharp pairwise A/C Fréchet lower overlap bound without assuming independence.
 Mathematical meaning: The full three-test model obeys the sharp pairwise A/C Fréchet lower overlap bound without assuming independence.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pC3 m-1<=pAC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_frechet_lower_bound :
  forall m : ThreeTestModel, pA3 m+pC3 m-1<=pAC3 m..
Proof.
  intro m.
  pose proof (Admissions.frechet_lower_bound (pair_AC3 m)) as H.
  rewrite triple_ac_first_marginal, triple_ac_second_marginal,
          triple_ac_joint_mass in H.
  exact H.
Qed.

(**
 [triple_ac_conditional_second_interval] (theorem) — Conditional C admission among A passers is a probability in [0,1] whenever the conditioning marginal is positive.
 Mathematical meaning: Conditional C admission among A passers is a probability in [0,1] whenever the conditioning marginal is positive.
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m -> 0<=Admissions.conditional_B_given_A (pair_AC3 m) /\ Admissions.conditional_B_given_A (pair_AC3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_conditional_second_interval :
  forall m : ThreeTestModel, 0<pA3 m -> 0<=Admissions.conditional_B_given_A (pair_AC3 m) /\ Admissions.conditional_B_given_A (pair_AC3 m)<=1..
Proof.
  intros m Hx.
  apply Admissions.conditional_B_given_A_unit_interval.
  rewrite triple_ac_first_marginal; exact Hx.
Qed.

(**
 [triple_ac_association_positive_iff] (theorem) — Positive A/C association is exactly strict positive excess overlap above the independent-product reference.
 Mathematical meaning: Positive A/C association is exactly strict positive excess overlap above the independent-product reference.
 Exact checked proposition: forall m : ThreeTestModel, 0<Admissions.admission_association (pair_AC3 m) <-> pA3 m*pC3 m<pAC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_association_positive_iff :
  forall m : ThreeTestModel, 0<Admissions.admission_association (pair_AC3 m) <-> pA3 m*pC3 m<pAC3 m..
Proof.
  intro m.
  rewrite (Admissions.admission_association_positive_iff_overlap (pair_AC3 m)).
  rewrite triple_ac_first_marginal.
  rewrite triple_ac_second_marginal.
  rewrite triple_ac_joint_mass.
  reflexivity.
Qed.

(**
 [triple_ac_association_negative_iff] (theorem) — Negative A/C association is exactly strict overlap below the independent-product reference.
 Mathematical meaning: Negative A/C association is exactly strict overlap below the independent-product reference.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_AC3 m)<0 <-> pAC3 m<pA3 m*pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_association_negative_iff :
  forall m : ThreeTestModel, Admissions.admission_association (pair_AC3 m)<0 <-> pAC3 m<pA3 m*pC3 m..
Proof.
  intro m.
  rewrite (Admissions.admission_association_negative_iff_overlap (pair_AC3 m)).
  rewrite triple_ac_first_marginal.
  rewrite triple_ac_second_marginal.
  rewrite triple_ac_joint_mass.
  reflexivity.
Qed.

(**
 [triple_ac_odds_one_iff_independent] (theorem) — When both discordant cells have positive product, the A/C odds ratio is one exactly at pairwise independence.
 Mathematical meaning: When both discordant cells have positive product, the A/C odds ratio is one exactly at pairwise independence.
 Exact checked proposition: forall m : ThreeTestModel, 0<Admissions.only_A (pair_AC3 m)*Admissions.only_B (pair_AC3 m) -> (Admissions.admission_odds_ratio (pair_AC3 m)=1 <-> pAC3 m=pA3 m*pC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_odds_one_iff_independent :
  forall m : ThreeTestModel, 0<Admissions.only_A (pair_AC3 m)*Admissions.only_B (pair_AC3 m) -> (Admissions.admission_odds_ratio (pair_AC3 m)=1 <-> pAC3 m=pA3 m*pC3 m)..
Proof.
  intros m Hpos.
  pose proof (Admissions.admission_odds_ratio_one_iff_independent (pair_AC3 m) Hpos) as H.
  rewrite triple_ac_joint_mass, triple_ac_first_marginal,
          triple_ac_second_marginal in H.
  exact H.
Qed.

(**
 [triple_ac_phi_unit_interval] (theorem) — With strictly positive Bernoulli variances, projected A/C phi correlation lies in [-1,1].
 Mathematical meaning: With strictly positive Bernoulli variances, projected A/C phi correlation lies in [-1,1].
 Exact checked proposition: forall m : ThreeTestModel, 0<pA3 m -> pA3 m<1 -> 0<pC3 m -> pC3 m<1 -> -1<=Admissions.admission_phi (pair_AC3 m) /\ Admissions.admission_phi (pair_AC3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_phi_unit_interval :
  forall m : ThreeTestModel, 0<pA3 m -> pA3 m<1 -> 0<pC3 m -> pC3 m<1 -> -1<=Admissions.admission_phi (pair_AC3 m) /\ Admissions.admission_phi (pair_AC3 m)<=1..
Proof.
  intros m Hx0 Hx1 Hy0 Hy1.
  apply Admissions.admission_phi_unit_interval;
  (rewrite triple_ac_first_marginal || rewrite triple_ac_second_marginal); assumption.
Qed.

(**
 [triple_ac_union_unit_interval] (theorem) — The projection of A/C admissions has a normalized nonnegative union probability at most one.
 Mathematical meaning: The projection of A/C admissions has a normalized nonnegative union probability at most one.
 Exact checked proposition: forall m : ThreeTestModel, 0<=Admissions.p_either (pair_AC3 m) /\ Admissions.p_either (pair_AC3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_ac_union_unit_interval :
  forall m : ThreeTestModel, 0<=Admissions.p_either (pair_AC3 m) /\ Admissions.p_either (pair_AC3 m)<=1..
Proof.
  intro m; split.
  - apply Admissions.union_nonnegative.
  - apply Admissions.union_at_most_one.
Qed.

(**
 [pair_BC3] (definition) — Forgetting the unused Boolean test leaves a normalized two-test B/C contingency distribution, with exact joint/first-only/second-only/neither cells.
 Mathematical meaning: Forgetting the unused Boolean test leaves a normalized two-test B/C contingency distribution, with exact joint/first-only/second-only/neither cells.
 Exact declaration: forall m : ThreeTestModel, pair_BC3 m : Admissions.TwoEventModel
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Construct the four disjoint marginal cell masses and close all record validity obligations using the normalized eight-outcome mass proof.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Definition pair_BC3 (m : ThreeTestModel) : Admissions.TwoEventModel.
Proof.
  refine {| Admissions.joint := mass3 m (true,true,true) + mass3 m (false,true,true);
            Admissions.only_A := mass3 m (true,true,false) + mass3 m (false,true,false);
            Admissions.only_B := mass3 m (true,false,true) + mass3 m (false,false,true);
            Admissions.neither := mass3 m (true,false,false) + mass3 m (false,false,false) |};
    triple_lra.
Defined.

(**
 [triple_bc_joint_mass] (theorem) — The B-C marginal overlap equals its original three-test event mass.
 Mathematical meaning: The B-C marginal overlap equals its original three-test event mass.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_both (pair_BC3 m) = pBC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_joint_mass :
  forall m : ThreeTestModel, Admissions.p_both (pair_BC3 m) = pBC3 m..
Proof.
  intros m;
  unfold Admissions.p_both, pair_BC3; simpl; triple_lra.
Qed.

(**
 [triple_bc_first_only_mass] (theorem) — Exactly B without C is the first marginal minus the pair intersection.
 Mathematical meaning: Exactly B without C is the first marginal minus the pair intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.only_A (pair_BC3 m) = pB3 m-pBC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_first_only_mass :
  forall m : ThreeTestModel, Admissions.only_A (pair_BC3 m) = pB3 m-pBC3 m..
Proof.
  intros m;
  unfold pair_BC3; simpl; triple_lra.
Qed.

(**
 [triple_bc_second_only_mass] (theorem) — Exactly C without B is the second marginal minus the pair intersection.
 Mathematical meaning: Exactly C without B is the second marginal minus the pair intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.only_B (pair_BC3 m) = pC3 m-pBC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_second_only_mass :
  forall m : ThreeTestModel, Admissions.only_B (pair_BC3 m) = pC3 m-pBC3 m..
Proof.
  intros m;
  unfold pair_BC3; simpl; triple_lra.
Qed.

(**
 [triple_bc_neither_mass] (theorem) — Neither B nor C is the complement of their union even when the omitted test succeeds.
 Mathematical meaning: Neither B nor C is the complement of their union even when the omitted test succeeds.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.neither (pair_BC3 m) = 1-(pB3 m+pC3 m-pBC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_neither_mass :
  forall m : ThreeTestModel, Admissions.neither (pair_BC3 m) = 1-(pB3 m+pC3 m-pBC3 m)..
Proof.
  intros m;
  unfold pair_BC3; simpl; triple_lra.
Qed.

(**
 [triple_bc_first_marginal] (theorem) — The certified two-test first-route marginal is exactly the B marginal in the full three-test model.
 Mathematical meaning: The certified two-test first-route marginal is exactly the B marginal in the full three-test model.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_A (pair_BC3 m) = pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_first_marginal :
  forall m : ThreeTestModel, Admissions.p_A (pair_BC3 m) = pB3 m..
Proof.
  intros m;
  unfold Admissions.p_A.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_first_only_mass.
  ring.
Qed.

(**
 [triple_bc_second_marginal] (theorem) — The certified two-test second-route marginal is exactly the C marginal in the full three-test model.
 Mathematical meaning: The certified two-test second-route marginal is exactly the C marginal in the full three-test model.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_B (pair_BC3 m) = pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_second_marginal :
  forall m : ThreeTestModel, Admissions.p_B (pair_BC3 m) = pC3 m..
Proof.
  intros m;
  unfold Admissions.p_B.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_second_only_mass.
  ring.
Qed.

(**
 [triple_bc_union_mass] (theorem) — The union of B and C is the sum of its marginals less their intersection.
 Mathematical meaning: The union of B and C is the sum of its marginals less their intersection.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_either (pair_BC3 m) = pB3 m+pC3 m-pBC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_union_mass :
  forall m : ThreeTestModel, Admissions.p_either (pair_BC3 m) = pB3 m+pC3 m-pBC3 m..
Proof.
  intros m;
  unfold Admissions.p_either.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_first_only_mass.
  rewrite triple_bc_second_only_mass.
  ring.
Qed.

(**
 [triple_bc_exclusive_mass] (theorem) — Exactly one of B or C succeeds with two-test mass p_first+p_second−2p_overlap.
 Mathematical meaning: Exactly one of B or C succeeds with two-test mass p_first+p_second−2p_overlap.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.p_exactly_one (pair_BC3 m) = pB3 m+pC3 m-2*pBC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_exclusive_mass :
  forall m : ThreeTestModel, Admissions.p_exactly_one (pair_BC3 m) = pB3 m+pC3 m-2*pBC3 m..
Proof.
  intros m;
  unfold Admissions.p_exactly_one.
  rewrite triple_bc_first_only_mass.
  rewrite triple_bc_second_only_mass.
  ring.
Qed.

(**
 [triple_bc_conditional_second_given_first] (theorem) — The original C given B admission rate is the projected two-event conditional probability.
 Mathematical meaning: The original C given B admission rate is the projected two-event conditional probability.
 Exact checked proposition: forall m : ThreeTestModel, 0<pB3 m -> Admissions.conditional_B_given_A (pair_BC3 m) = pBC3 m/pB3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_conditional_second_given_first :
  forall m : ThreeTestModel, 0<pB3 m -> Admissions.conditional_B_given_A (pair_BC3 m) = pBC3 m/pB3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_B_given_A.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_first_marginal.
  reflexivity.
Qed.

(**
 [triple_bc_conditional_first_given_second] (theorem) — The B given C admission rate agrees with the projected two-event conditional.
 Mathematical meaning: The B given C admission rate agrees with the projected two-event conditional.
 Exact checked proposition: forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_A_given_B (pair_BC3 m) = pBC3 m/pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_conditional_first_given_second :
  forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_A_given_B (pair_BC3 m) = pBC3 m/pC3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_A_given_B.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_second_marginal.
  reflexivity.
Qed.

(**
 [triple_bc_conditional_overlap_given_union] (theorem) — The chance of admission by both B and C, conditional on at least one, has the exact overlap/union ratio.
 Mathematical meaning: The chance of admission by both B and C, conditional on at least one, has the exact overlap/union ratio.
 Exact checked proposition: forall m : ThreeTestModel, 0<pB3 m+pC3 m-pBC3 m -> Admissions.conditional_both_given_either (pair_BC3 m) = pBC3 m/(pB3 m+pC3 m-pBC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_conditional_overlap_given_union :
  forall m : ThreeTestModel, 0<pB3 m+pC3 m-pBC3 m -> Admissions.conditional_both_given_either (pair_BC3 m) = pBC3 m/(pB3 m+pC3 m-pBC3 m)..
Proof.
  intros m _.
  unfold Admissions.conditional_both_given_either.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_union_mass.
  reflexivity.
Qed.

(**
 [triple_bc_conditional_notfirst_given_second] (theorem) — Among C passers, the B rejection fraction is the second-only cell divided by its second marginal.
 Mathematical meaning: Among C passers, the B rejection fraction is the second-only cell divided by its second marginal.
 Exact checked proposition: forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_not_A_given_B (pair_BC3 m) = (pC3 m-pBC3 m)/pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_conditional_notfirst_given_second :
  forall m : ThreeTestModel, 0<pC3 m -> Admissions.conditional_not_A_given_B (pair_BC3 m) = (pC3 m-pBC3 m)/pC3 m..
Proof.
  intros m _.
  unfold Admissions.conditional_not_A_given_B.
  rewrite triple_bc_second_only_mass.
  rewrite triple_bc_second_marginal.
  reflexivity.
Qed.

(**
 [triple_bc_conditional_second_given_notfirst] (theorem) — Among those not admitted by B, the chance of C admission has a complement-stratum denominator.
 Mathematical meaning: Among those not admitted by B, the chance of C admission has a complement-stratum denominator.
 Exact checked proposition: forall m : ThreeTestModel, 0<1-pB3 m -> Admissions.admission_B_given_not_A (pair_BC3 m) = (pC3 m-pBC3 m)/(1-pB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_conditional_second_given_notfirst :
  forall m : ThreeTestModel, 0<1-pB3 m -> Admissions.admission_B_given_not_A (pair_BC3 m) = (pC3 m-pBC3 m)/(1-pB3 m)..
Proof.
  intros m _.
  unfold Admissions.admission_B_given_not_A, Admissions.admission_not_A_mass.
  rewrite triple_bc_second_only_mass.
  rewrite triple_bc_neither_mass.
  replace ((pC3 m-pBC3 m)+(1-(pB3 m+pC3 m-pBC3 m))) with (1-pB3 m) by ring.
  reflexivity.
Qed.

(**
 [triple_bc_conditional_first_given_notsecond] (theorem) — Among those not admitted by C, the chance of B admission uses the other complement stratum.
 Mathematical meaning: Among those not admitted by C, the chance of B admission uses the other complement stratum.
 Exact checked proposition: forall m : ThreeTestModel, 0<1-pC3 m -> Admissions.admission_A_given_not_B (pair_BC3 m) = (pB3 m-pBC3 m)/(1-pC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_conditional_first_given_notsecond :
  forall m : ThreeTestModel, 0<1-pC3 m -> Admissions.admission_A_given_not_B (pair_BC3 m) = (pB3 m-pBC3 m)/(1-pC3 m)..
Proof.
  intros m _.
  unfold Admissions.admission_A_given_not_B, Admissions.admission_not_B_mass.
  rewrite triple_bc_first_only_mass.
  rewrite triple_bc_neither_mass.
  replace ((pB3 m-pBC3 m)+(1-(pB3 m+pC3 m-pBC3 m))) with (1-pC3 m) by ring.
  reflexivity.
Qed.

(**
 [triple_bc_association_covariance] (theorem) — The B/C 2×2 cross-product association is exactly joint probability minus the product of marginals.
 Mathematical meaning: The B/C 2×2 cross-product association is exactly joint probability minus the product of marginals.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_BC3 m) = pBC3 m-pB3 m*pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_association_covariance :
  forall m : ThreeTestModel, Admissions.admission_association (pair_BC3 m) = pBC3 m-pB3 m*pC3 m..
Proof.
  intro m.
  rewrite Admissions.admission_association_covariance.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_first_marginal.
  rewrite triple_bc_second_marginal.
  reflexivity.
Qed.

(**
 [triple_bc_independence_criterion] (theorem) — Independence of B and C in the three-route population is equivalent to a vanishing projected contingency association.
 Mathematical meaning: Independence of B and C in the three-route population is equivalent to a vanishing projected contingency association.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_BC3 m)=0 <-> pBC3 m=pB3 m*pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_independence_criterion :
  forall m : ThreeTestModel, Admissions.admission_association (pair_BC3 m)=0 <-> pBC3 m=pB3 m*pC3 m..
Proof.
  intros m.
  rewrite (Admissions.admission_association_zero_iff_independence (pair_BC3 m)).
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_first_marginal.
  rewrite triple_bc_second_marginal.
  reflexivity.
Qed.

(**
 [triple_bc_union_independent_reference] (theorem) — The independent-reference union estimate differs from the actual B/C union by exactly the admission association.
 Mathematical meaning: The independent-reference union estimate differs from the actual B/C union by exactly the admission association.
 Exact checked proposition: forall m : ThreeTestModel, pB3 m+pC3 m-pBC3 m = pB3 m+pC3 m-pB3 m*pC3 m-Admissions.admission_association (pair_BC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_union_independent_reference :
  forall m : ThreeTestModel, pB3 m+pC3 m-pBC3 m = pB3 m+pC3 m-pB3 m*pC3 m-Admissions.admission_association (pair_BC3 m)..
Proof.
  intro m.
  rewrite triple_bc_association_covariance.
  ring.
Qed.

(**
 [triple_bc_first_indicator_variance] (theorem) — The Bernoulli success variance of route B in the two-route projection matches its full-model marginal.
 Mathematical meaning: The Bernoulli success variance of route B in the two-route projection matches its full-model marginal.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_indicator_variance_A (pair_BC3 m) = pB3 m*(1-pB3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_first_indicator_variance :
  forall m : ThreeTestModel, Admissions.admission_indicator_variance_A (pair_BC3 m) = pB3 m*(1-pB3 m)..
Proof.
  intro m.
  unfold Admissions.admission_indicator_variance_A.
  rewrite triple_bc_first_marginal.
  reflexivity.
Qed.

(**
 [triple_bc_second_indicator_variance] (theorem) — The Bernoulli success variance of route C in the two-route projection matches its full-model marginal.
 Mathematical meaning: The Bernoulli success variance of route C in the two-route projection matches its full-model marginal.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_indicator_variance_B (pair_BC3 m) = pC3 m*(1-pC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_second_indicator_variance :
  forall m : ThreeTestModel, Admissions.admission_indicator_variance_B (pair_BC3 m) = pC3 m*(1-pC3 m)..
Proof.
  intro m.
  unfold Admissions.admission_indicator_variance_B.
  rewrite triple_bc_second_marginal.
  reflexivity.
Qed.

(**
 [triple_bc_odds_ratio] (theorem) — The B/C odds ratio is the exact concordant/discordant probability cross-product for its marginalized cells.
 Mathematical meaning: The B/C odds ratio is the exact concordant/discordant probability cross-product for its marginalized cells.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_odds_ratio (pair_BC3 m) = pBC3 m*(1-(pB3 m+pC3 m-pBC3 m))/(((pB3 m-pBC3 m)*(pC3 m-pBC3 m))).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_odds_ratio :
  forall m : ThreeTestModel, Admissions.admission_odds_ratio (pair_BC3 m) = pBC3 m*(1-(pB3 m+pC3 m-pBC3 m))/(((pB3 m-pBC3 m)*(pC3 m-pBC3 m)))..
Proof.
  intro m.
  unfold Admissions.admission_odds_ratio.
  rewrite triple_bc_joint_mass.
  rewrite triple_bc_neither_mass.
  rewrite triple_bc_first_only_mass.
  rewrite triple_bc_second_only_mass.
  reflexivity.
Qed.

(**
 [triple_bc_phi_coefficient] (theorem) — The projected B/C phi coefficient equals the standardized joint-minus-product association with its own Bernoulli variances.
 Mathematical meaning: The projected B/C phi coefficient equals the standardized joint-minus-product association with its own Bernoulli variances.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_phi (pair_BC3 m) = (pBC3 m-pB3 m*pC3 m)/sqrt ((pB3 m*(1-pB3 m))*(pC3 m*(1-pC3 m))).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_phi_coefficient :
  forall m : ThreeTestModel, Admissions.admission_phi (pair_BC3 m) = (pBC3 m-pB3 m*pC3 m)/sqrt ((pB3 m*(1-pB3 m))*(pC3 m*(1-pC3 m)))..
Proof.
  intro m.
  unfold Admissions.admission_phi.
  rewrite triple_bc_association_covariance.
  rewrite triple_bc_first_indicator_variance.
  rewrite triple_bc_second_indicator_variance.
  reflexivity.
Qed.

(**
 [triple_bc_frechet_lower_bound] (theorem) — The full three-test model obeys the sharp pairwise B/C Fréchet lower overlap bound without assuming independence.
 Mathematical meaning: The full three-test model obeys the sharp pairwise B/C Fréchet lower overlap bound without assuming independence.
 Exact checked proposition: forall m : ThreeTestModel, pB3 m+pC3 m-1<=pBC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_frechet_lower_bound :
  forall m : ThreeTestModel, pB3 m+pC3 m-1<=pBC3 m..
Proof.
  intro m.
  pose proof (Admissions.frechet_lower_bound (pair_BC3 m)) as H.
  rewrite triple_bc_first_marginal, triple_bc_second_marginal,
          triple_bc_joint_mass in H.
  exact H.
Qed.

(**
 [triple_bc_conditional_second_interval] (theorem) — Conditional C admission among B passers is a probability in [0,1] whenever the conditioning marginal is positive.
 Mathematical meaning: Conditional C admission among B passers is a probability in [0,1] whenever the conditioning marginal is positive.
 Exact checked proposition: forall m : ThreeTestModel, 0<pB3 m -> 0<=Admissions.conditional_B_given_A (pair_BC3 m) /\ Admissions.conditional_B_given_A (pair_BC3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_conditional_second_interval :
  forall m : ThreeTestModel, 0<pB3 m -> 0<=Admissions.conditional_B_given_A (pair_BC3 m) /\ Admissions.conditional_B_given_A (pair_BC3 m)<=1..
Proof.
  intros m Hx.
  apply Admissions.conditional_B_given_A_unit_interval.
  rewrite triple_bc_first_marginal; exact Hx.
Qed.

(**
 [triple_bc_association_positive_iff] (theorem) — Positive B/C association is exactly strict positive excess overlap above the independent-product reference.
 Mathematical meaning: Positive B/C association is exactly strict positive excess overlap above the independent-product reference.
 Exact checked proposition: forall m : ThreeTestModel, 0<Admissions.admission_association (pair_BC3 m) <-> pB3 m*pC3 m<pBC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_association_positive_iff :
  forall m : ThreeTestModel, 0<Admissions.admission_association (pair_BC3 m) <-> pB3 m*pC3 m<pBC3 m..
Proof.
  intro m.
  rewrite (Admissions.admission_association_positive_iff_overlap (pair_BC3 m)).
  rewrite triple_bc_first_marginal.
  rewrite triple_bc_second_marginal.
  rewrite triple_bc_joint_mass.
  reflexivity.
Qed.

(**
 [triple_bc_association_negative_iff] (theorem) — Negative B/C association is exactly strict overlap below the independent-product reference.
 Mathematical meaning: Negative B/C association is exactly strict overlap below the independent-product reference.
 Exact checked proposition: forall m : ThreeTestModel, Admissions.admission_association (pair_BC3 m)<0 <-> pBC3 m<pB3 m*pC3 m.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_association_negative_iff :
  forall m : ThreeTestModel, Admissions.admission_association (pair_BC3 m)<0 <-> pBC3 m<pB3 m*pC3 m..
Proof.
  intro m.
  rewrite (Admissions.admission_association_negative_iff_overlap (pair_BC3 m)).
  rewrite triple_bc_first_marginal.
  rewrite triple_bc_second_marginal.
  rewrite triple_bc_joint_mass.
  reflexivity.
Qed.

(**
 [triple_bc_odds_one_iff_independent] (theorem) — When both discordant cells have positive product, the B/C odds ratio is one exactly at pairwise independence.
 Mathematical meaning: When both discordant cells have positive product, the B/C odds ratio is one exactly at pairwise independence.
 Exact checked proposition: forall m : ThreeTestModel, 0<Admissions.only_A (pair_BC3 m)*Admissions.only_B (pair_BC3 m) -> (Admissions.admission_odds_ratio (pair_BC3 m)=1 <-> pBC3 m=pB3 m*pC3 m).
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_odds_one_iff_independent :
  forall m : ThreeTestModel, 0<Admissions.only_A (pair_BC3 m)*Admissions.only_B (pair_BC3 m) -> (Admissions.admission_odds_ratio (pair_BC3 m)=1 <-> pBC3 m=pB3 m*pC3 m)..
Proof.
  intros m Hpos.
  pose proof (Admissions.admission_odds_ratio_one_iff_independent (pair_BC3 m) Hpos) as H.
  rewrite triple_bc_joint_mass, triple_bc_first_marginal,
          triple_bc_second_marginal in H.
  exact H.
Qed.

(**
 [triple_bc_phi_unit_interval] (theorem) — With strictly positive Bernoulli variances, projected B/C phi correlation lies in [-1,1].
 Mathematical meaning: With strictly positive Bernoulli variances, projected B/C phi correlation lies in [-1,1].
 Exact checked proposition: forall m : ThreeTestModel, 0<pB3 m -> pB3 m<1 -> 0<pC3 m -> pC3 m<1 -> -1<=Admissions.admission_phi (pair_BC3 m) /\ Admissions.admission_phi (pair_BC3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_phi_unit_interval :
  forall m : ThreeTestModel, 0<pB3 m -> pB3 m<1 -> 0<pC3 m -> pC3 m<1 -> -1<=Admissions.admission_phi (pair_BC3 m) /\ Admissions.admission_phi (pair_BC3 m)<=1..
Proof.
  intros m Hx0 Hx1 Hy0 Hy1.
  apply Admissions.admission_phi_unit_interval;
  (rewrite triple_bc_first_marginal || rewrite triple_bc_second_marginal); assumption.
Qed.

(**
 [triple_bc_union_unit_interval] (theorem) — The projection of B/C admissions has a normalized nonnegative union probability at most one.
 Mathematical meaning: The projection of B/C admissions has a normalized nonnegative union probability at most one.
 Exact checked proposition: forall m : ThreeTestModel, 0<=Admissions.p_either (pair_BC3 m) /\ Admissions.p_either (pair_BC3 m)<=1.
 Premises and side conditions: The underlying ThreeTestModel is an exact,
 finite, nonnegative, unit-normalized distribution. Any additional strict
 positivity premise required for conditional rates, odds or phi is written
 directly in the theorem statement; zero-denominator total-real arithmetic
 must not be confused with a conditional probability interpretation.
 Proof/definition method: Delegate pairwise probability logic to the existing Admissions lemmas whenever possible; use elementary ring normalization for the audited eight-cell bridge identities.
 Library reuse: Admissions.TwoEventModel and its existing conditional,
 independence, odds and covariance theorems; ThreeTestAdmissions.triple_lra,
 the canonical FiniteUnion.finite_prob and FiniteSum.finite_sum; Stdlib.Lra.
 Boundary: This is a discrete Boolean contingency-table fact, not a proof
 of multivariate normal tails, Gaussian conditional distributions or empirical
 IQ-population admissions rates.
 *)
Theorem triple_bc_union_unit_interval :
  forall m : ThreeTestModel, 0<=Admissions.p_either (pair_BC3 m) /\ Admissions.p_either (pair_BC3 m)<=1..
Proof.
  intro m; split.
  - apply Admissions.union_nonnegative.
  - apply Admissions.union_at_most_one.
Qed.

