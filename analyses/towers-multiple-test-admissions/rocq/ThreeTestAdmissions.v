(** Module: ThreeTestAdmissions.v
  Purpose: Verify three-test admission probabilities, exact multiplicity
  counts, full inclusion-exclusion, Fréchet and Bonferroni inequalities,
  all under a concrete finite outcome model rather than Gaussian axioms.
  Mathematical representation: Each of the eight Boolean success patterns
  is an outcome in a canonical list. A real weight function supplies atom
  masses, constrained to nonnegative values and unit FiniteSum total.
  Explicit hypotheses: Nonnegative weights and exact mass normalization
  are record fields. No correlation, conditional independence or Gaussian
  premise is silently supplied.
  Library use: FiniteSum.finite_sum and FiniteUnion.finite_prob supply
  the sole finite integration/event-mass engines; Stdlib List/Bool, Reals,
  Lra, Psatz provide canonical data structures and proof automation.
  Limitations: The theorem statements concern exact finite admissions
  event arithmetic. They do not establish bivariate/trivariate Gaussian
  tails, normal quantiles or empirical admission probabilities.
  Reproduction: scripts/compile_rocq.sh with pinned Rocq Prover 9.2,
  after FiniteUnion.v and Admissions.v in the canonical build.
  AI disclosure: OpenAI ChatGPT assisted with mathematical statement,
  source code and proof drafting. Only CI kernel checks establish validity.
*)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import FiniteSum FiniteUnion Admissions.
Import ListNotations.
Open Scope R_scope.

(** [triple_outcome] models the three Boolean admissions decisions.
 Mathematical meaning: One outcome records whether tests A, B and C accept.
 Exact declaration: Type alias for a three-component Boolean tuple.
 Premises and side conditions: No assumptions on event dependence are
 imposed by the type. Atomic mass properties are modeled separately.
 Proof/definition method: Use Stdlib.Bool and the product type directly.
 Library reuse: Stdlib.Bool and Rocq's built-in product type; no new records
 or inductive event algebra are introduced at the outcome level.
 Boundary: These are finite event labels, not Gaussian random variables. *)
Definition triple_outcome : Type := (bool * bool * bool)%type.

(** [triple_cases] lists all eight possible three-route event patterns.
 Mathematical meaning: The finite sample contains each event pattern once.
 Exact declaration: Eight distinct Boolean triples in descending pattern order.
 Premises and side conditions: Each entry contributes its mass exactly once;
 no sorting, deduplication or random sampling is performed.
 Proof/definition method: Stdlib.List syntax for an explicit eight-element list.
 Library reuse: FiniteSum and Stdlib.List rather than a custom fold/recursion.
 Boundary: Does not assert a population stochastic model. *)
Definition triple_cases : list triple_outcome :=
  [(true,true,true); (true,true,false); (true,false,true); (true,false,false);
   (false,true,true); (false,true,false); (false,false,true); (false,false,false)].

(** [ThreeTestModel] is a normalized three-test finite probability model.
 Mathematical meaning: Eight Boolean event-pattern masses are represented
 by one function and checked nonnegativity and unit-total evidence.
 Exact declaration: A weight function with nonnegative entries and a
 FiniteSum total equal to one on the canonical eight cases.
 Premises and side conditions: The record cannot be constructed without
 proofs of normalization and nonnegative mass on every outcome.
 Proof/definition method: Reuse FiniteSum.finite_sum rather than writing
 a new probability aggregator, ring, integration or normalization algorithm.
 Library reuse: FiniteSum.finite_sum, Stdlib.Bool, and Reals.
 Boundary: This is an exact discrete probability space, not Gaussian data. *)
Record ThreeTestModel := {
  mass3 : triple_outcome -> R;
  mass3_nonnegative : forall x, 0 <= mass3 x;
  mass3_normalized : FiniteSum.finite_sum mass3 triple_cases = 1
}.

(** [testA3] projects the first Boolean admission decision.
 Mathematical meaning: The first route's success indicator depends only on
 the first component of an already-enumerated outcome pattern.
 Exact declaration: The first component of a Boolean triple.
 Premises and side conditions: No nonnegativity is required for projections.
 Proof/definition method: Use ordinary Rocq product pattern matching.
 Library reuse: Stdlib product matching; no custom event recursion.
 Boundary: A Boolean event only, not a real-valued IQ predictor. *)
Definition testA3 (x : triple_outcome) : bool :=
  let '(a,b,c) := x in a.
(** [testB3] projects the second Boolean admission decision.
 Mathematical meaning: The second route's success is the second coordinate.
 Exact declaration: The second Boolean component of a three-test pattern.
 Premises and side conditions: The finite outcome list is given separately.
 Proof/definition method: Use canonical product pattern matching.
 Library reuse: Stdlib.Bool and built-in tuple constructors.
 Boundary: A deterministic event predicate, not Gaussian. *)
Definition testB3 (x : triple_outcome) : bool :=
  let '(a,b,c) := x in b.
(** [testC3] projects the third Boolean admission decision.
 Mathematical meaning: The final route's success is the last coordinate.
 Exact declaration: The third Boolean component of a three-test pattern.
 Premises and side conditions: No additional stochastic assumptions.
 Proof/definition method: Product projections are standard Rocq operations.
 Library reuse: Stdlib.Bool and built-in tuple constructs.
 Boundary: Deterministic sample event only, not empirical test evidence. *)
Definition testC3 (x : triple_outcome) : bool :=
  let '(a,b,c) := x in c.

(** [triple_prob] assigns mass to an event using the shared event library.
 Mathematical meaning: The weighted finite-event mass is taken on the
 complete enumerated three-event sample; zero mass is permitted.
 Exact declaration: FiniteUnion.finite_prob applied to triple_cases.
 Premises and side conditions: The model record supplies nonnegative,
 normalized atomic masses, but the definition itself is total.
 Proof/definition method: Transparent wrapper around canonical event mass.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum.
 Boundary: Finite weighted probability only, never a Gaussian integral. *)
Definition triple_prob (m:ThreeTestModel) (e:triple_outcome->bool) : R :=
  FiniteUnion.finite_prob (mass3 m) triple_cases e.

(** [pA3] represents first test admission marginal as an exact mass of a Boolean event.
 Mathematical meaning: first test admission marginal, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pA3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pA3 (m : ThreeTestModel) : R := triple_prob m testA3.

(** [pB3] represents second test admission marginal as an exact mass of a Boolean event.
 Mathematical meaning: second test admission marginal, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pB3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pB3 (m : ThreeTestModel) : R := triple_prob m testB3.

(** [pC3] represents third test admission marginal as an exact mass of a Boolean event.
 Mathematical meaning: third test admission marginal, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pC3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pC3 (m : ThreeTestModel) : R := triple_prob m testC3.

(** [pAB3] represents joint admission on routes A and B as an exact mass of a Boolean event.
 Mathematical meaning: joint admission on routes A and B, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pAB3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pAB3 (m : ThreeTestModel) : R := triple_prob m (fun x => andb (testA3 x) (testB3 x)).

(** [pAC3] represents joint admission on routes A and C as an exact mass of a Boolean event.
 Mathematical meaning: joint admission on routes A and C, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pAC3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pAC3 (m : ThreeTestModel) : R := triple_prob m (fun x => andb (testA3 x) (testC3 x)).

(** [pBC3] represents joint admission on routes B and C as an exact mass of a Boolean event.
 Mathematical meaning: joint admission on routes B and C, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pBC3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pBC3 (m : ThreeTestModel) : R := triple_prob m (fun x => andb (testB3 x) (testC3 x)).

(** [pABC3] represents all three admission routes jointly as an exact mass of a Boolean event.
 Mathematical meaning: all three admission routes jointly, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pABC3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pABC3 (m : ThreeTestModel) : R := triple_prob m (fun x => andb (testA3 x) (andb (testB3 x) (testC3 x))).

(** [pUnion3] represents at least one admission success as an exact mass of a Boolean event.
 Mathematical meaning: at least one admission success, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pUnion3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pUnion3 (m : ThreeTestModel) : R := triple_prob m (fun x => orb (testA3 x) (orb (testB3 x) (testC3 x))).

(** [pNone3] represents no admission success as an exact mass of a Boolean event.
 Mathematical meaning: no admission success, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pNone3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pNone3 (m : ThreeTestModel) : R := triple_prob m (fun x => negb (orb (testA3 x) (orb (testB3 x) (testC3 x)))).

(** [pOne3] represents exactly one successful route as an exact mass of a Boolean event.
 Mathematical meaning: exactly one successful route, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pOne3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pOne3 (m : ThreeTestModel) : R := triple_prob m (fun x => match x with (true,false,false) | (false,true,false) | (false,false,true) => true | _ => false end).

(** [pTwo3] represents exactly two successful routes as an exact mass of a Boolean event.
 Mathematical meaning: exactly two successful routes, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pTwo3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pTwo3 (m : ThreeTestModel) : R := triple_prob m (fun x => match x with (true,true,false) | (true,false,true) | (false,true,true) => true | _ => false end).

(** [pAtLeastTwo3] represents at least two successful routes as an exact mass of a Boolean event.
 Mathematical meaning: at least two successful routes, with no double-counting of an outcome.
 Exact declaration: triple_prob applied to the canonical pAtLeastTwo3 event.
 Premises and side conditions: Only the provided ThreeTestModel; normalized
 mass and nonnegative weights are guaranteed by its record fields.
 Proof/definition method: A transparent application of the shared library's
 Boolean event predicate and finite event probability.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum and Stdlib.Bool.
 Boundary: This is finite admission-route probability, not a certified
 Gaussian-tail result or population-based admissions estimate. *)
Definition pAtLeastTwo3 (m : ThreeTestModel) : R := triple_prob m (fun x => match x with (true,true,true) | (true,true,false) | (true,false,true) | (false,true,true) => true | _ => false end).

(* Central proof normalizer. This tactic only unfolds the three-report
   Boolean events into the eight canonical cells; it creates no axioms,
   no bespoke summation and no additional trusted proof mechanism. *)
Ltac triple_lra :=
  match goal with
  | [ m : ThreeTestModel |- _ ] =>
    pose proof (mass3_normalized m) as Htotal;
    pose proof (mass3_nonnegative m (true,true,true)) as H111;
    pose proof (mass3_nonnegative m (true,true,false)) as H110;
    pose proof (mass3_nonnegative m (true,false,true)) as H101;
    pose proof (mass3_nonnegative m (true,false,false)) as H100;
    pose proof (mass3_nonnegative m (false,true,true)) as H011;
    pose proof (mass3_nonnegative m (false,true,false)) as H010;
    pose proof (mass3_nonnegative m (false,false,true)) as H001;
    pose proof (mass3_nonnegative m (false,false,false)) as H000
  end;
  cbv [pA3 pB3 pC3 pAB3 pAC3 pBC3 pABC3 pUnion3 pNone3
       pOne3 pTwo3 pAtLeastTwo3 triple_prob
       FiniteUnion.finite_prob FiniteUnion.indicator
       FiniteSum.finite_sum triple_cases
       testA3 testB3 testC3 List.map List.fold_right
       Bool.andb Bool.orb Bool.negb] in *;
  lra.

(**
 [triple_first_marginal_atoms] (theorem) — The first admission route is the sum of the four compatible atomic outcomes.
 Mathematical meaning: The first admission route is the sum of the four compatible atomic outcomes.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (true,false,false).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_first_marginal_atoms :
  forall m : ThreeTestModel, pA3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (true,false,false).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_second_marginal_atoms] (theorem) — The second admission route is the sum of the four compatible atomic outcomes.
 Mathematical meaning: The second admission route is the sum of the four compatible atomic outcomes.
 Exact checked proposition: forall m : ThreeTestModel, pB3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (false,true,true)+mass3 m (false,true,false).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_second_marginal_atoms :
  forall m : ThreeTestModel, pB3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (false,true,true)+mass3 m (false,true,false).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_third_marginal_atoms] (theorem) — The third admission route is the sum of the four compatible atomic outcomes.
 Mathematical meaning: The third admission route is the sum of the four compatible atomic outcomes.
 Exact checked proposition: forall m : ThreeTestModel, pC3 m = mass3 m (true,true,true)+mass3 m (true,false,true)+mass3 m (false,true,true)+mass3 m (false,false,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_third_marginal_atoms :
  forall m : ThreeTestModel, pC3 m = mass3 m (true,true,true)+mass3 m (true,false,true)+mass3 m (false,true,true)+mass3 m (false,false,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_first_second_overlap_atoms] (theorem) — Pairwise first–second overlap counts both possible third-route outcomes.
 Mathematical meaning: Pairwise first–second overlap counts both possible third-route outcomes.
 Exact checked proposition: forall m : ThreeTestModel, pAB3 m = mass3 m (true,true,true)+mass3 m (true,true,false).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_first_second_overlap_atoms :
  forall m : ThreeTestModel, pAB3 m = mass3 m (true,true,true)+mass3 m (true,true,false).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_first_third_overlap_atoms] (theorem) — Pairwise first–third overlap counts both possible second-route outcomes.
 Mathematical meaning: Pairwise first–third overlap counts both possible second-route outcomes.
 Exact checked proposition: forall m : ThreeTestModel, pAC3 m = mass3 m (true,true,true)+mass3 m (true,false,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_first_third_overlap_atoms :
  forall m : ThreeTestModel, pAC3 m = mass3 m (true,true,true)+mass3 m (true,false,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_second_third_overlap_atoms] (theorem) — Pairwise second–third overlap counts both possible first-route outcomes.
 Mathematical meaning: Pairwise second–third overlap counts both possible first-route outcomes.
 Exact checked proposition: forall m : ThreeTestModel, pBC3 m = mass3 m (true,true,true)+mass3 m (false,true,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_second_third_overlap_atoms :
  forall m : ThreeTestModel, pBC3 m = mass3 m (true,true,true)+mass3 m (false,true,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_all_three_atoms] (theorem) — The three-way overlap is exactly the all-admitted atomic outcome.
 Mathematical meaning: The three-way overlap is exactly the all-admitted atomic outcome.
 Exact checked proposition: forall m : ThreeTestModel, pABC3 m = mass3 m (true,true,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_all_three_atoms :
  forall m : ThreeTestModel, pABC3 m = mass3 m (true,true,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_atoms] (theorem) — The any-admission probability sums the seven nonempty event atoms.
 Mathematical meaning: The any-admission probability sums the seven nonempty event atoms.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (true,false,false)+mass3 m (false,true,true)+mass3 m (false,true,false)+mass3 m (false,false,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_atoms :
  forall m : ThreeTestModel, pUnion3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (true,false,false)+mass3 m (false,true,true)+mass3 m (false,true,false)+mass3 m (false,false,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_none_atoms] (theorem) — The no-admission event has exactly the all-false atomic probability.
 Mathematical meaning: The no-admission event has exactly the all-false atomic probability.
 Exact checked proposition: forall m : ThreeTestModel, pNone3 m = mass3 m (false,false,false).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_none_atoms :
  forall m : ThreeTestModel, pNone3 m = mass3 m (false,false,false).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_exactly_one_atoms] (theorem) — Exactly one admission comprises the three singleton success patterns.
 Mathematical meaning: Exactly one admission comprises the three singleton success patterns.
 Exact checked proposition: forall m : ThreeTestModel, pOne3 m = mass3 m (true,false,false)+mass3 m (false,true,false)+mass3 m (false,false,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_exactly_one_atoms :
  forall m : ThreeTestModel, pOne3 m = mass3 m (true,false,false)+mass3 m (false,true,false)+mass3 m (false,false,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_exactly_two_atoms] (theorem) — Exactly two admissions comprises the three success-pair patterns.
 Mathematical meaning: Exactly two admissions comprises the three success-pair patterns.
 Exact checked proposition: forall m : ThreeTestModel, pTwo3 m = mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (false,true,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_exactly_two_atoms :
  forall m : ThreeTestModel, pTwo3 m = mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (false,true,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_at_least_two_atoms] (theorem) — At least two admissions comprises the three double and single triple success patterns.
 Mathematical meaning: At least two admissions comprises the three double and single triple success patterns.
 Exact checked proposition: forall m : ThreeTestModel, pAtLeastTwo3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (false,true,true).
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_at_least_two_atoms :
  forall m : ThreeTestModel, pAtLeastTwo3 m = mass3 m (true,true,true)+mass3 m (true,true,false)+mass3 m (true,false,true)+mass3 m (false,true,true).
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_multiplicity_expectation] (theorem) — Expected number of successes is the weighted sum of exactly-one, exactly-two and exactly-three probabilities.
 Mathematical meaning: Expected number of successes is the weighted sum of exactly-one, exactly-two and exactly-three probabilities.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m = pOne3 m+2*pTwo3 m+3*pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_multiplicity_expectation :
  forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m = pOne3 m+2*pTwo3 m+3*pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_multiplicity_partition] (theorem) — The union partitions into exactly one, exactly two, or all three successes.
 Mathematical meaning: The union partitions into exactly one, exactly two, or all three successes.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m = pOne3 m+pTwo3 m+pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_multiplicity_partition :
  forall m : ThreeTestModel, pUnion3 m = pOne3 m+pTwo3 m+pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_atleast_two_partition] (theorem) — The at-least-two event is a disjoint union of double and triple success.
 Mathematical meaning: The at-least-two event is a disjoint union of double and triple success.
 Exact checked proposition: forall m : ThreeTestModel, pAtLeastTwo3 m = pTwo3 m+pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_atleast_two_partition :
  forall m : ThreeTestModel, pAtLeastTwo3 m = pTwo3 m+pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_pair_overlap_multiplicity] (theorem) — Summing the three pair intersections counts double successes once and triple successes three times.
 Mathematical meaning: Summing the three pair intersections counts double successes once and triple successes three times.
 Exact checked proposition: forall m : ThreeTestModel, pAB3 m+pAC3 m+pBC3 m = pTwo3 m+3*pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_pair_overlap_multiplicity :
  forall m : ThreeTestModel, pAB3 m+pAC3 m+pBC3 m = pTwo3 m+3*pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_total_multiplicity_partition] (theorem) — The four disjoint exact-admission-count events exhaust total mass.
 Mathematical meaning: The four disjoint exact-admission-count events exhaust total mass.
 Exact checked proposition: forall m : ThreeTestModel, pNone3 m+pOne3 m+pTwo3 m+pABC3 m = 1.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_total_multiplicity_partition :
  forall m : ThreeTestModel, pNone3 m+pOne3 m+pTwo3 m+pABC3 m = 1.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_none_complement] (theorem) — The probability of any admission plus no admission is one.
 Mathematical meaning: The probability of any admission plus no admission is one.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m+pNone3 m = 1.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_none_complement :
  forall m : ThreeTestModel, pUnion3 m+pNone3 m = 1.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_inclusion_exclusion] (theorem) — Three-way inclusion-exclusion correctly subtracts pair overlaps and restores the triple intersection.
 Mathematical meaning: Three-way inclusion-exclusion correctly subtracts pair overlaps and restores the triple intersection.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m+pAB3 m+pAC3 m+pBC3 m = pA3 m+pB3 m+pC3 m+pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_inclusion_exclusion :
  forall m : ThreeTestModel, pUnion3 m+pAB3 m+pAC3 m+pBC3 m = pA3 m+pB3 m+pC3 m+pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_sum_marginals_threshold] (theorem) — The total of the three admission marginals equals union plus at-least-two plus triple intersection.
 Mathematical meaning: The total of the three admission marginals equals union plus at-least-two plus triple intersection.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m = pUnion3 m+pAtLeastTwo3 m+pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_sum_marginals_threshold :
  forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m = pUnion3 m+pAtLeastTwo3 m+pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_atleast_two_pair_masses] (theorem) — The at-least-two event mass equals all pairwise overlaps minus two copies of triple overlap.
 Mathematical meaning: The at-least-two event mass equals all pairwise overlaps minus two copies of triple overlap.
 Exact checked proposition: forall m : ThreeTestModel, pAtLeastTwo3 m+2*pABC3 m = pAB3 m+pAC3 m+pBC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_atleast_two_pair_masses :
  forall m : ThreeTestModel, pAtLeastTwo3 m+2*pABC3 m = pAB3 m+pAC3 m+pBC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_exclusive_from_marginals] (theorem) — Exactly-one success is determined by marginal totals, pairwise overlap totals and triple overlap.
 Mathematical meaning: Exactly-one success is determined by marginal totals, pairwise overlap totals and triple overlap.
 Exact checked proposition: forall m : ThreeTestModel, pOne3 m+2*(pAB3 m+pAC3 m+pBC3 m) = pA3 m+pB3 m+pC3 m+3*pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_exclusive_from_marginals :
  forall m : ThreeTestModel, pOne3 m+2*(pAB3 m+pAC3 m+pBC3 m) = pA3 m+pB3 m+pC3 m+3*pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_double_from_marginals] (theorem) — Exactly-two success is the sum of pairwise intersections less three copies of triple intersection.
 Mathematical meaning: Exactly-two success is the sum of pairwise intersections less three copies of triple intersection.
 Exact checked proposition: forall m : ThreeTestModel, pTwo3 m+3*pABC3 m = pAB3 m+pAC3 m+pBC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_double_from_marginals :
  forall m : ThreeTestModel, pTwo3 m+3*pABC3 m = pAB3 m+pAC3 m+pBC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_none_inclusion_exclusion] (theorem) — No admission has a closed complement formula in marginal, pairwise and triple probabilities.
 Mathematical meaning: No admission has a closed complement formula in marginal, pairwise and triple probabilities.
 Exact checked proposition: forall m : ThreeTestModel, pNone3 m+pA3 m+pB3 m+pC3 m+pABC3 m = 1+pAB3 m+pAC3 m+pBC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_none_inclusion_exclusion :
  forall m : ThreeTestModel, pNone3 m+pA3 m+pB3 m+pC3 m+pABC3 m = 1+pAB3 m+pAC3 m+pBC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_atleast_two_gap] (theorem) — The increase from exactly two to at least two is exactly the triple overlap.
 Mathematical meaning: The increase from exactly two to at least two is exactly the triple overlap.
 Exact checked proposition: forall m : ThreeTestModel, pAtLeastTwo3 m-pTwo3 m = pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_atleast_two_gap :
  forall m : ThreeTestModel, pAtLeastTwo3 m-pTwo3 m = pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_exclusive_gap] (theorem) — The union's increment beyond exactly-one successes is exactly at-least-two successes.
 Mathematical meaning: The union's increment beyond exactly-one successes is exactly at-least-two successes.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m-pOne3 m = pAtLeastTwo3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_exclusive_gap :
  forall m : ThreeTestModel, pUnion3 m-pOne3 m = pAtLeastTwo3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_frechet_three_lower] (theorem) — Three-event Fréchet inequality: the triple intersection is at least the sum of marginals minus two.
 Mathematical meaning: Three-event Fréchet inequality: the triple intersection is at least the sum of marginals minus two.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m-2 <= pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_frechet_three_lower :
  forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m-2 <= pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_frechet_three_upper_first] (theorem) — A three-way intersection is contained in the first marginal.
 Mathematical meaning: A three-way intersection is contained in the first marginal.
 Exact checked proposition: forall m : ThreeTestModel, pABC3 m <= pA3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_frechet_three_upper_first :
  forall m : ThreeTestModel, pABC3 m <= pA3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_frechet_three_upper_second] (theorem) — A three-way intersection is contained in the second marginal.
 Mathematical meaning: A three-way intersection is contained in the second marginal.
 Exact checked proposition: forall m : ThreeTestModel, pABC3 m <= pB3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_frechet_three_upper_second :
  forall m : ThreeTestModel, pABC3 m <= pB3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_frechet_three_upper_third] (theorem) — A three-way intersection is contained in the third marginal.
 Mathematical meaning: A three-way intersection is contained in the third marginal.
 Exact checked proposition: forall m : ThreeTestModel, pABC3 m <= pC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_frechet_three_upper_third :
  forall m : ThreeTestModel, pABC3 m <= pC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_intersection_below_first_second] (theorem) — The three-way overlap cannot exceed the first-second overlap.
 Mathematical meaning: The three-way overlap cannot exceed the first-second overlap.
 Exact checked proposition: forall m : ThreeTestModel, pABC3 m <= pAB3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_intersection_below_first_second :
  forall m : ThreeTestModel, pABC3 m <= pAB3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_intersection_below_first_third] (theorem) — The three-way overlap cannot exceed the first-third overlap.
 Mathematical meaning: The three-way overlap cannot exceed the first-third overlap.
 Exact checked proposition: forall m : ThreeTestModel, pABC3 m <= pAC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_intersection_below_first_third :
  forall m : ThreeTestModel, pABC3 m <= pAC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_intersection_below_second_third] (theorem) — The three-way overlap cannot exceed the second-third overlap.
 Mathematical meaning: The three-way overlap cannot exceed the second-third overlap.
 Exact checked proposition: forall m : ThreeTestModel, pABC3 m <= pBC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_intersection_below_second_third :
  forall m : ThreeTestModel, pABC3 m <= pBC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_three_union_bound] (theorem) — The union probability is bounded by the sum of all marginal probabilities.
 Mathematical meaning: The union probability is bounded by the sum of all marginal probabilities.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_three_union_bound :
  forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_unit_upper] (theorem) — A three-route admission union has probability no greater than one.
 Mathematical meaning: A three-route admission union has probability no greater than one.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m <= 1.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_unit_upper :
  forall m : ThreeTestModel, pUnion3 m <= 1.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_first_lower] (theorem) — A union always contains its first admission route.
 Mathematical meaning: A union always contains its first admission route.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_first_lower :
  forall m : ThreeTestModel, pA3 m <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_second_lower] (theorem) — A union always contains its second admission route.
 Mathematical meaning: A union always contains its second admission route.
 Exact checked proposition: forall m : ThreeTestModel, pB3 m <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_second_lower :
  forall m : ThreeTestModel, pB3 m <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_third_lower] (theorem) — A union always contains its third admission route.
 Mathematical meaning: A union always contains its third admission route.
 Exact checked proposition: forall m : ThreeTestModel, pC3 m <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_third_lower :
  forall m : ThreeTestModel, pC3 m <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_first_bonferroni_lower] (theorem) — Adding the third admission route cannot reduce the first-two union probability.
 Mathematical meaning: Adding the third admission route cannot reduce the first-two union probability.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pB3 m-pAB3 m <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_first_bonferroni_lower :
  forall m : ThreeTestModel, pA3 m+pB3 m-pAB3 m <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_second_bonferroni_lower] (theorem) — Adding the second admission route cannot reduce the first–third union.
 Mathematical meaning: Adding the second admission route cannot reduce the first–third union.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pC3 m-pAC3 m <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_second_bonferroni_lower :
  forall m : ThreeTestModel, pA3 m+pC3 m-pAC3 m <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_third_bonferroni_lower] (theorem) — Adding the first admission route cannot reduce the second–third union.
 Mathematical meaning: Adding the first admission route cannot reduce the second–third union.
 Exact checked proposition: forall m : ThreeTestModel, pB3 m+pC3 m-pBC3 m <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_third_bonferroni_lower :
  forall m : ThreeTestModel, pB3 m+pC3 m-pBC3 m <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_bonferroni_pair_lower] (theorem) — The second-order Bonferroni approximation is a lower bound for the three-route union.
 Mathematical meaning: The second-order Bonferroni approximation is a lower bound for the three-route union.
 Exact checked proposition: forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m-(pAB3 m+pAC3 m+pBC3 m) <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_bonferroni_pair_lower :
  forall m : ThreeTestModel, pA3 m+pB3 m+pC3 m-(pAB3 m+pAC3 m+pBC3 m) <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_bonferroni_pair_upper_first] (theorem) — Subtracting two overlaps associated with the first test gives a valid union upper bound.
 Mathematical meaning: Subtracting two overlaps associated with the first test gives a valid union upper bound.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m-pAB3 m-pAC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_bonferroni_pair_upper_first :
  forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m-pAB3 m-pAC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_bonferroni_pair_upper_second] (theorem) — Subtracting overlaps associated with the second test gives a valid union upper bound.
 Mathematical meaning: Subtracting overlaps associated with the second test gives a valid union upper bound.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m-pAB3 m-pBC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_bonferroni_pair_upper_second :
  forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m-pAB3 m-pBC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_bonferroni_pair_upper_third] (theorem) — Subtracting overlaps associated with the third test gives a valid union upper bound.
 Mathematical meaning: Subtracting overlaps associated with the third test gives a valid union upper bound.
 Exact checked proposition: forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m-pAC3 m-pBC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_bonferroni_pair_upper_third :
  forall m : ThreeTestModel, pUnion3 m <= pA3 m+pB3 m+pC3 m-pAC3 m-pBC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_two_successes_below_pair_sum] (theorem) — At least two admissions has probability no greater than the sum of pair overlaps.
 Mathematical meaning: At least two admissions has probability no greater than the sum of pair overlaps.
 Exact checked proposition: forall m : ThreeTestModel, pAtLeastTwo3 m <= pAB3 m+pAC3 m+pBC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_two_successes_below_pair_sum :
  forall m : ThreeTestModel, pAtLeastTwo3 m <= pAB3 m+pAC3 m+pBC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_two_successes_below_half_marginals] (theorem) — The chance of two or more admissions is at most half the total marginal success count.
 Mathematical meaning: The chance of two or more admissions is at most half the total marginal success count.
 Exact checked proposition: forall m : ThreeTestModel, 2*pAtLeastTwo3 m <= pA3 m+pB3 m+pC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_two_successes_below_half_marginals :
  forall m : ThreeTestModel, 2*pAtLeastTwo3 m <= pA3 m+pB3 m+pC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_two_successes_contains_first_pair] (theorem) — Any first-second joint success is included in the at-least-two success event.
 Mathematical meaning: Any first-second joint success is included in the at-least-two success event.
 Exact checked proposition: forall m : ThreeTestModel, pAB3 m <= pAtLeastTwo3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_two_successes_contains_first_pair :
  forall m : ThreeTestModel, pAB3 m <= pAtLeastTwo3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_two_successes_contains_second_pair] (theorem) — Any first-third joint success is included in the at-least-two success event.
 Mathematical meaning: Any first-third joint success is included in the at-least-two success event.
 Exact checked proposition: forall m : ThreeTestModel, pAC3 m <= pAtLeastTwo3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_two_successes_contains_second_pair :
  forall m : ThreeTestModel, pAC3 m <= pAtLeastTwo3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_two_successes_contains_third_pair] (theorem) — Any second-third joint success is included in the at-least-two success event.
 Mathematical meaning: Any second-third joint success is included in the at-least-two success event.
 Exact checked proposition: forall m : ThreeTestModel, pBC3 m <= pAtLeastTwo3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_two_successes_contains_third_pair :
  forall m : ThreeTestModel, pBC3 m <= pAtLeastTwo3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_exactly_one_nonnegative] (theorem) — Exactly-one admission probability is nonnegative under nonnegative atomic weights.
 Mathematical meaning: Exactly-one admission probability is nonnegative under nonnegative atomic weights.
 Exact checked proposition: forall m : ThreeTestModel, 0 <= pOne3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_exactly_one_nonnegative :
  forall m : ThreeTestModel, 0 <= pOne3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_exactly_two_nonnegative] (theorem) — Exactly-two admission probability is nonnegative under nonnegative atomic weights.
 Mathematical meaning: Exactly-two admission probability is nonnegative under nonnegative atomic weights.
 Exact checked proposition: forall m : ThreeTestModel, 0 <= pTwo3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_exactly_two_nonnegative :
  forall m : ThreeTestModel, 0 <= pTwo3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_three_nonnegative] (theorem) — Three-way joint admission probability is nonnegative.
 Mathematical meaning: Three-way joint admission probability is nonnegative.
 Exact checked proposition: forall m : ThreeTestModel, 0 <= pABC3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_three_nonnegative :
  forall m : ThreeTestModel, 0 <= pABC3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_none_nonnegative] (theorem) — The no-admission event has nonnegative probability.
 Mathematical meaning: The no-admission event has nonnegative probability.
 Exact checked proposition: forall m : ThreeTestModel, 0 <= pNone3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_none_nonnegative :
  forall m : ThreeTestModel, 0 <= pNone3 m.
Proof.
  intros m; triple_lra.
Qed.

(**
 [triple_union_nonnegative] (theorem) — The union has nonnegative probability.
 Mathematical meaning: The union has nonnegative probability.
 Exact checked proposition: forall m : ThreeTestModel, 0 <= pUnion3 m.
 Premises and side conditions: Each of the eight atomic event masses is
 nonnegative and the sample weight total equals one, encoded in the
 ThreeTestModel rather than assumed by informal statistical terminology.
 Proof/definition method: Unfold the standardized Boolean-event masses,
 then apply Stdlib.Lra to the eight-cell linear identity or inequality
 using the actual record nonnegativity and normalization evidence.
 Library reuse: FiniteUnion.finite_prob, FiniteSum.finite_sum, Stdlib.Bool,
 Stdlib.List and the canonical trusted Lra real-linear tactic; no extra
 summation implementation, Gaussian oracle or unproved model constraint.
 Boundary: Exact finite-event probability only; this does not prove a
 multivariate Gaussian integral, empirical admission rate or normal cutoff.
 *)
Theorem triple_union_nonnegative :
  forall m : ThreeTestModel, 0 <= pUnion3 m.
Proof.
  intros m; triple_lra.
Qed.

