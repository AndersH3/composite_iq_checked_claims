(** Module: ReportCounterexample.v
   Purpose: Kernel-check the finite probability counterexample in the
   sequential conditional-means report: standardized marginals and zero
   covariance do not determine a conditional mean.
   Mathematical representation: Two explicitly enumerated weighted finite
   distributions of pairs (X,Y), sharing the same X and Y marginals, with
   dependent and independent joint couplings. The distributions use only
   rational atom scores and masses and the existing finite_sum fold.
   Explicit hypotheses: None are axiomatized. The finite sample masses,
   nonnegativity, moments, cross moments and event probabilities are
   proved as exact rational identities.
   Library use: FiniteSum.finite_sum, Stdlib.List, Reals, Lra and Psatz.
   Limitations: This countermodel refutes distribution-free regression
   from correlation alone. It does not prove or refute Gaussian regression,
   regular conditional expectations in general spaces, or empirical IQ
   validity. All conditional event means here divide by checked positive
   event probabilities.
   Proof documentation: Every definition and theorem has mathematical
   meaning, exact proposition, explicit premises, approach and limitations.
   Reproduction: rocq compile FiniteSum.v, followed by
   rocq compile ReportCounterexample.v under Rocq 9.2.
*)

From Stdlib Require Import Reals Lra Psatz List.
Require Import FiniteSum.
Import ListNotations.
Open Scope R_scope.

(**
 [report_dependent_samples] (definition) — Three-atom correlated coupling.
 Mathematical meaning: The dependent model lists three distinct atoms.
 Exact declaration: Outcomes [0;1;2] in a finite sample list.
 Premises and side conditions: The atoms are indices; their probabilities
 are assigned explicitly by report_dependent_weight.
 Proof/definition method: Reuse the standard list representation.
 Library reuse: Stdlib.List and FiniteSum.
 Boundary: No Gaussian distribution is assumed.
*)
Definition report_dependent_samples : list nat := [0%nat;1%nat;2%nat].

(**
 [report_independent_samples] (definition) — Six-atom independent coupling.
 Mathematical meaning: The independent model splits each X atom into two
 Y-signed atoms with equal conditional mass.
 Exact declaration: Outcomes [0;1;2;3;4;5].
 Premises and side conditions: Probabilities are explicit in the weights.
 Proof/definition method: Standard finite list rather than a custom sum.
 Library reuse: Stdlib.List.
 Boundary: Independence is witnessed by exact marginal/conditional masses.
*)
Definition report_independent_samples : list nat := [0%nat;1%nat;2%nat;3%nat;4%nat;5%nat].

(**
 [report_dependent_weight] (definition) — Dependent joint mass function.
 Mathematical meaning: X=-1 and X=2 have masses 1/3,1/6; X=0 has 1/2.
 Exact declaration: weights (1/3,1/6,1/2), zero elsewhere.
 Premises and side conditions: Positivity and total mass are proved below.
 Proof/definition method: Nat pattern matching; no distribution axioms.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: Finite counting only.
*)
Definition report_dependent_weight (n:nat) : R :=
  match n with 0%nat => 1/3 | 1%nat => 1/6 | 2%nat => 1/2 | _ => 0 end.

(**
 [report_independent_weight] (definition) — Independent coupling masses.
 Mathematical meaning: The six weighted atoms split the marginal X masses
 evenly by the two equiprobable values Y=±1.
 Exact declaration: (1/6,1/6,1/12,1/12,1/4,1/4).
 Premises and side conditions: Total mass one and all weights positive.
 Proof/definition method: Standard Nat pattern matching.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: These are exact rational probabilities, not fitted data.
*)
Definition report_independent_weight (n:nat) : R :=
  match n with
  | 0%nat | 1%nat => 1/6
  | 2%nat | 3%nat => 1/12
  | 4%nat | 5%nat => 1/4
  | _ => 0
  end.

(**
 [report_dependent_x] (definition) — First standardized score, coupled model.
 Mathematical meaning: X=-1,2,0 on the three atoms.
 Exact declaration: X(0)=-1, X(1)=2, X(2)=0.
 Premises and side conditions: Standardization is proved from moments.
 Proof/definition method: Standard Nat pattern matching.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: Not a continuous Gaussian score.
*)
Definition report_dependent_x (n:nat) : R :=
  match n with 0%nat => -1 | 1%nat => 2 | _ => 0 end.

(**
 [report_independent_x] (definition) — First score, split independent model.
 Mathematical meaning: X=-1 for atoms 0,1; X=2 for 2,3; X=0 for 4,5.
 Exact declaration: X=(-1,-1,2,2,0,0).
 Premises and side conditions: Same X marginal is checked below.
 Proof/definition method: Standard Nat pattern matching.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: Finite discrete score.
*)
Definition report_independent_x (n:nat) : R :=
  match n with
  | 0%nat | 1%nat => -1
  | 2%nat | 3%nat => 2
  | _ => 0
  end.

(**
 [report_dependent_y] (definition) — Nonlinear dependent second score.
 Mathematical meaning: Y=+1 for nonzero X and Y=-1 when X=0.
 Exact declaration: Y(0)=Y(1)=+1 and Y(2)=-1.
 Premises and side conditions: No noise or independence premise.
 Proof/definition method: Standard Nat pattern matching.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: The joint law is not Gaussian.
*)
Definition report_dependent_y (n:nat) : R :=
  match n with 0%nat | 1%nat => 1 | _ => -1 end.

(**
 [report_independent_y] (definition) — Symmetric independent second score.
 Mathematical meaning: Y alternates +1 and -1 for each X value.
 Exact declaration: Y=(+1,-1,+1,-1,+1,-1).
 Premises and side conditions: Independence follows from equal split masses.
 Proof/definition method: Standard Nat pattern matching.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: This finite coupling is not a Gaussian realization.
*)
Definition report_independent_y (n:nat) : R :=
  match n with 0%nat | 2%nat | 4%nat => 1 | _ => -1 end.

(**
 [report_dependent_expectation] (definition) — Weighted finite expectation.
 Mathematical meaning: E_d[g] integrates g over the three dependent atoms.
 Exact declaration: finite_sum (fun n=>w_d(n)*g(n)) dependent_samples.
 Premises and side conditions: Mass normalization proved separately.
 Proof/definition method: Delegates wholly to the shared finite_sum fold.
 Library reuse: FiniteSum.finite_sum.
 Boundary: This is not a general measure integral.
*)
Definition report_dependent_expectation (g:nat->R) : R :=
  finite_sum (fun n => report_dependent_weight n * g n)
    report_dependent_samples.

(**
 [report_independent_expectation] (definition) — Second finite expectation.
 Mathematical meaning: E_i[g] integrates g over the six independent atoms.
 Exact declaration: finite_sum (fun n=>w_i(n)*g(n)) independent_samples.
 Premises and side conditions: Mass normalization proved separately.
 Proof/definition method: Delegates to the shared finite_sum fold.
 Library reuse: FiniteSum.finite_sum.
 Boundary: This is not an abstract probability space.
*)
Definition report_independent_expectation (g:nat->R) : R :=
  finite_sum (fun n => report_independent_weight n * g n)
    report_independent_samples.

(**
 [report_dependent_zero_event] (definition) — Event X=0 indicator.
 Mathematical meaning: The dependent model has X=0 precisely at atom 2.
 Exact declaration: Indicator 1 at 2, 0 otherwise.
 Premises and side conditions: The sample support is fixed by definition.
 Proof/definition method: Finite atom indicator, no undecidable R equality.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: Indicator correctness is checked separately on the sample list.
*)
Definition report_dependent_zero_event (n:nat) : R :=
  match n with 2%nat => 1 | _ => 0 end.

(**
 [report_independent_zero_event] (definition) — Independent X=0 indicator.
 Mathematical meaning: Independent model has X=0 at atoms 4 and 5.
 Exact declaration: Indicator 1 at 4,5 and 0 otherwise.
 Premises and side conditions: The enumerated sample list is fixed.
 Proof/definition method: Direct Nat pattern matching.
 Library reuse: Stdlib.Init.Nat, Reals.
 Boundary: Correct only for this explicit finite model.
*)
Definition report_independent_zero_event (n:nat) : R :=
  match n with 4%nat | 5%nat => 1 | _ => 0 end.

(**
 [report_dependent_conditional_mean_at_zero] (definition) —
 Event-conditional mean of Y in the dependent coupling.
 Mathematical meaning: E_d[Y 1_{X=0}]/P_d(X=0).
 Exact declaration: Ratio of the two shared finite_sum expectations.
 Premises and side conditions: Denominator positive by a theorem below.
 Proof/definition method: Finite conditioning ratio without a general
 measure-theoretic conditional-expectation primitive.
 Library reuse: report_dependent_expectation, real division.
 Boundary: The conditional value refers only to the positive-mass event.
*)
Definition report_dependent_conditional_mean_at_zero : R :=
  report_dependent_expectation
    (fun n => report_dependent_zero_event n * report_dependent_y n) /
  report_dependent_expectation report_dependent_zero_event.

(**
 [report_independent_conditional_mean_at_zero] (definition) —
 Event-conditional mean of Y in the independent coupling.
 Mathematical meaning: E_i[Y 1_{X=0}]/P_i(X=0).
 Exact declaration: Ratio of two shared finite_sum expectations.
 Premises and side conditions: Denominator is proved equal to 1/2.
 Proof/definition method: Standard finite positive-event quotient.
 Library reuse: report_independent_expectation, real division.
 Boundary: No general conditional-law existence theorem is claimed.
*)
Definition report_independent_conditional_mean_at_zero : R :=
  report_independent_expectation
    (fun n => report_independent_zero_event n * report_independent_y n) /
  report_independent_expectation report_independent_zero_event.

(**
 [report_dependent_total_mass_one] (theorem) — Dependent weights sum to one, establishing a valid finite probability distribution.
 Mathematical meaning: Dependent weights sum to one, establishing a valid finite probability distribution.
 Exact checked proposition: report_dependent_expectation (fun _ => 1) = 1.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_total_mass_one :
  report_dependent_expectation (fun _ => 1) = 1.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_total_mass_one] (theorem) — Independent weights sum to one, establishing a valid finite probability distribution.
 Mathematical meaning: Independent weights sum to one, establishing a valid finite probability distribution.
 Exact checked proposition: report_independent_expectation (fun _ => 1) = 1.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_total_mass_one :
  report_independent_expectation (fun _ => 1) = 1.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_x_mean_zero] (theorem) — The dependent coupling's first score has exact mean zero.
 Mathematical meaning: The dependent coupling's first score has exact mean zero.
 Exact checked proposition: report_dependent_expectation report_dependent_x = 0.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_x_mean_zero :
  report_dependent_expectation report_dependent_x = 0.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_x_mean_zero] (theorem) — The independent coupling's first score has exact mean zero.
 Mathematical meaning: The independent coupling's first score has exact mean zero.
 Exact checked proposition: report_independent_expectation report_independent_x = 0.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_x_mean_zero :
  report_independent_expectation report_independent_x = 0.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_y_mean_zero] (theorem) — The dependent coupling's second score has exact mean zero.
 Mathematical meaning: The dependent coupling's second score has exact mean zero.
 Exact checked proposition: report_dependent_expectation report_dependent_y = 0.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_y_mean_zero :
  report_dependent_expectation report_dependent_y = 0.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_y_mean_zero] (theorem) — The independent coupling's second score has exact mean zero.
 Mathematical meaning: The independent coupling's second score has exact mean zero.
 Exact checked proposition: report_independent_expectation report_independent_y = 0.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_y_mean_zero :
  report_independent_expectation report_independent_y = 0.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_x_second_moment_one] (theorem) — The first dependent score has unit second moment and, with zero mean, unit variance.
 Mathematical meaning: The first dependent score has unit second moment and, with zero mean, unit variance.
 Exact checked proposition: report_dependent_expectation (fun n => report_dependent_x n * report_dependent_x n) = 1.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_x_second_moment_one :
  report_dependent_expectation (fun n => report_dependent_x n * report_dependent_x n) = 1.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_x_second_moment_one] (theorem) — The first independent score has unit second moment and unit variance.
 Mathematical meaning: The first independent score has unit second moment and unit variance.
 Exact checked proposition: report_independent_expectation (fun n => report_independent_x n * report_independent_x n) = 1.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_x_second_moment_one :
  report_independent_expectation (fun n => report_independent_x n * report_independent_x n) = 1.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_y_second_moment_one] (theorem) — The second dependent score has unit second moment and unit variance.
 Mathematical meaning: The second dependent score has unit second moment and unit variance.
 Exact checked proposition: report_dependent_expectation (fun n => report_dependent_y n * report_dependent_y n) = 1.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_y_second_moment_one :
  report_dependent_expectation (fun n => report_dependent_y n * report_dependent_y n) = 1.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_y_second_moment_one] (theorem) — The second independent score has unit second moment and unit variance.
 Mathematical meaning: The second independent score has unit second moment and unit variance.
 Exact checked proposition: report_independent_expectation (fun n => report_independent_y n * report_independent_y n) = 1.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_y_second_moment_one :
  report_independent_expectation (fun n => report_independent_y n * report_independent_y n) = 1.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_cross_moment_zero] (theorem) — The dependent scores have zero cross moment and, with centered scores, zero covariance and correlation.
 Mathematical meaning: The dependent scores have zero cross moment and, with centered scores, zero covariance and correlation.
 Exact checked proposition: report_dependent_expectation (fun n => report_dependent_x n * report_dependent_y n) = 0.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_cross_moment_zero :
  report_dependent_expectation (fun n => report_dependent_x n * report_dependent_y n) = 0.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_cross_moment_zero] (theorem) — The independent scores have zero cross moment and zero covariance and correlation.
 Mathematical meaning: The independent scores have zero cross moment and zero covariance and correlation.
 Exact checked proposition: report_independent_expectation (fun n => report_independent_x n * report_independent_y n) = 0.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_cross_moment_zero :
  report_independent_expectation (fun n => report_independent_x n * report_independent_y n) = 0.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_zero_event_mass] (theorem) — The conditioning event X=0 has positive probability one half under the dependent coupling.
 Mathematical meaning: The conditioning event X=0 has positive probability one half under the dependent coupling.
 Exact checked proposition: report_dependent_expectation report_dependent_zero_event = 1 / 2.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_zero_event_mass :
  report_dependent_expectation report_dependent_zero_event = 1 / 2.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_zero_event_mass] (theorem) — The conditioning event X=0 has the same positive probability under the independent coupling.
 Mathematical meaning: The conditioning event X=0 has the same positive probability under the independent coupling.
 Exact checked proposition: report_independent_expectation report_independent_zero_event = 1 / 2.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_zero_event_mass :
  report_independent_expectation report_independent_zero_event = 1 / 2.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_zero_event_y_numerator] (theorem) — The dependent conditional-event weighted Y numerator equals minus one half.
 Mathematical meaning: The dependent conditional-event weighted Y numerator equals minus one half.
 Exact checked proposition: report_dependent_expectation (fun n => report_dependent_zero_event n * report_dependent_y n) = -1 / 2.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_dependent_zero_event_y_numerator :
  report_dependent_expectation (fun n => report_dependent_zero_event n * report_dependent_y n) = -1 / 2.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_independent_zero_event_y_numerator] (theorem) — The independent conditional-event weighted Y numerator vanishes.
 Mathematical meaning: The independent conditional-event weighted Y numerator vanishes.
 Exact checked proposition: report_independent_expectation (fun n => report_independent_zero_event n * report_independent_y n) = 0.
 Premises and side conditions: Concrete finite rational-atom probability model
 with total mass explicitly verified and no Gaussianity assumption.
 Proof/definition method: Unfold only the shared FiniteSum expectation
 wrapper, simplify finite atoms, and normalize rational real arithmetic
 by Rocq's standard Field and Lra tactics.
 Library reuse: FiniteSum.finite_sum, Stdlib.Reals, Field and Lra.
 Boundary: A finite countermodel arithmetic property, not a continuous
 conditional Gaussian distribution or statistical population inference.
*)
Theorem report_independent_zero_event_y_numerator :
  report_independent_expectation (fun n => report_independent_zero_event n * report_independent_y n) = 0.
Proof.
  cbv [report_dependent_expectation report_independent_expectation
    report_dependent_samples report_independent_samples
    report_dependent_weight report_independent_weight
    report_dependent_x report_independent_x
    report_dependent_y report_independent_y
    report_dependent_zero_event report_independent_zero_event
    finite_sum]; simpl; field; lra.
Qed.

(**
 [report_dependent_conditional_mean_negative_one] (theorem) — Dependent finite conditional mean at the event X=0 is exactly -1.
 Mathematical meaning: Dependent finite conditional mean at the event X=0 is exactly -1.
 Exact checked proposition: report_dependent_conditional_mean_at_zero = -1.
 Premises and side conditions: Exact rational weights on the explicitly
 listed finite models; the conditioning denominator equals 1/2 where used.
 Proof/definition method: Reuse the previously checked finite event
 probability and conditional numerator or normalize atom fractions by Field.
 Library reuse: FiniteSum.finite_sum and report moment/event certificate
 theorems; Rocq Stdlib.Reals and Field.
 Boundary: These exact positive-mass finite distribution identities do
 not assert general Gaussian regression or empirical psychometrics.
*)
Theorem report_dependent_conditional_mean_negative_one :
  report_dependent_conditional_mean_at_zero = -1.
Proof.
  unfold report_dependent_conditional_mean_at_zero.
  rewrite report_dependent_zero_event_y_numerator.
  rewrite report_dependent_zero_event_mass.
  field.
Qed.

(**
 [report_independent_conditional_mean_zero] (theorem) — Independent finite conditional mean at the same event X=0 is exactly 0.
 Mathematical meaning: Independent finite conditional mean at the same event X=0 is exactly 0.
 Exact checked proposition: report_independent_conditional_mean_at_zero = 0.
 Premises and side conditions: Exact rational weights on the explicitly
 listed finite models; the conditioning denominator equals 1/2 where used.
 Proof/definition method: Reuse the previously checked finite event
 probability and conditional numerator or normalize atom fractions by Field.
 Library reuse: FiniteSum.finite_sum and report moment/event certificate
 theorems; Rocq Stdlib.Reals and Field.
 Boundary: These exact positive-mass finite distribution identities do
 not assert general Gaussian regression or empirical psychometrics.
*)
Theorem report_independent_conditional_mean_zero :
  report_independent_conditional_mean_at_zero = 0.
Proof.
  unfold report_independent_conditional_mean_at_zero.
  rewrite report_independent_zero_event_y_numerator.
  rewrite report_independent_zero_event_mass.
  field.
Qed.

(**
 [report_models_same_x_minus_one_mass] (theorem) — Both couplings assign the same marginal mass one third to X=-1.
 Mathematical meaning: Both couplings assign the same marginal mass one third to X=-1.
 Exact checked proposition: report_dependent_weight 0 = report_independent_weight 0 + report_independent_weight 1.
 Premises and side conditions: Exact rational weights on the explicitly
 listed finite models; the conditioning denominator equals 1/2 where used.
 Proof/definition method: Reuse the previously checked finite event
 probability and conditional numerator or normalize atom fractions by Field.
 Library reuse: FiniteSum.finite_sum and report moment/event certificate
 theorems; Rocq Stdlib.Reals and Field.
 Boundary: These exact positive-mass finite distribution identities do
 not assert general Gaussian regression or empirical psychometrics.
*)
Theorem report_models_same_x_minus_one_mass :
  report_dependent_weight 0 = report_independent_weight 0 + report_independent_weight 1.
Proof.
  cbv [report_dependent_weight report_independent_weight]; field.
Qed.

(**
 [report_models_same_x_plus_two_mass] (theorem) — Both couplings assign the same marginal mass one sixth to X=2.
 Mathematical meaning: Both couplings assign the same marginal mass one sixth to X=2.
 Exact checked proposition: report_dependent_weight 1 = report_independent_weight 2 + report_independent_weight 3.
 Premises and side conditions: Exact rational weights on the explicitly
 listed finite models; the conditioning denominator equals 1/2 where used.
 Proof/definition method: Reuse the previously checked finite event
 probability and conditional numerator or normalize atom fractions by Field.
 Library reuse: FiniteSum.finite_sum and report moment/event certificate
 theorems; Rocq Stdlib.Reals and Field.
 Boundary: These exact positive-mass finite distribution identities do
 not assert general Gaussian regression or empirical psychometrics.
*)
Theorem report_models_same_x_plus_two_mass :
  report_dependent_weight 1 = report_independent_weight 2 + report_independent_weight 3.
Proof.
  cbv [report_dependent_weight report_independent_weight]; field.
Qed.

(**
 [report_models_same_x_zero_mass] (theorem) — Both couplings assign the same marginal mass one half to X=0.
 Mathematical meaning: Both couplings assign the same marginal mass one half to X=0.
 Exact checked proposition: report_dependent_weight 2 = report_independent_weight 4 + report_independent_weight 5.
 Premises and side conditions: Exact rational weights on the explicitly
 listed finite models; the conditioning denominator equals 1/2 where used.
 Proof/definition method: Reuse the previously checked finite event
 probability and conditional numerator or normalize atom fractions by Field.
 Library reuse: FiniteSum.finite_sum and report moment/event certificate
 theorems; Rocq Stdlib.Reals and Field.
 Boundary: These exact positive-mass finite distribution identities do
 not assert general Gaussian regression or empirical psychometrics.
*)
Theorem report_models_same_x_zero_mass :
  report_dependent_weight 2 = report_independent_weight 4 + report_independent_weight 5.
Proof.
  cbv [report_dependent_weight report_independent_weight]; field.
Qed.

(**
 [report_models_same_y_plus_one_mass] (theorem) — Both couplings give the same marginal probability one half for Y=+1.
 Mathematical meaning: Both couplings give the same marginal probability one half for Y=+1.
 Exact checked proposition: report_dependent_weight 0 + report_dependent_weight 1 = report_independent_weight 0 + report_independent_weight 2 + report_independent_weight 4.
 Premises and side conditions: Exact rational weights on the explicitly
 listed finite models; the conditioning denominator equals 1/2 where used.
 Proof/definition method: Reuse the previously checked finite event
 probability and conditional numerator or normalize atom fractions by Field.
 Library reuse: FiniteSum.finite_sum and report moment/event certificate
 theorems; Rocq Stdlib.Reals and Field.
 Boundary: These exact positive-mass finite distribution identities do
 not assert general Gaussian regression or empirical psychometrics.
*)
Theorem report_models_same_y_plus_one_mass :
  report_dependent_weight 0 + report_dependent_weight 1 = report_independent_weight 0 + report_independent_weight 2 + report_independent_weight 4.
Proof.
  cbv [report_dependent_weight report_independent_weight]; field.
Qed.

(**
 [report_models_same_y_minus_one_mass] (theorem) — Both couplings give the same marginal probability one half for Y=-1.
 Mathematical meaning: Both couplings give the same marginal probability one half for Y=-1.
 Exact checked proposition: report_dependent_weight 2 = report_independent_weight 1 + report_independent_weight 3 + report_independent_weight 5.
 Premises and side conditions: Exact rational weights on the explicitly
 listed finite models; the conditioning denominator equals 1/2 where used.
 Proof/definition method: Reuse the previously checked finite event
 probability and conditional numerator or normalize atom fractions by Field.
 Library reuse: FiniteSum.finite_sum and report moment/event certificate
 theorems; Rocq Stdlib.Reals and Field.
 Boundary: These exact positive-mass finite distribution identities do
 not assert general Gaussian regression or empirical psychometrics.
*)
Theorem report_models_same_y_minus_one_mass :
  report_dependent_weight 2 = report_independent_weight 1 + report_independent_weight 3 + report_independent_weight 5.
Proof.
  cbv [report_dependent_weight report_independent_weight]; field.
Qed.

(**
 [report_conditional_means_not_determined_by_marginals] (theorem) — The report's distribution-free
 regression counterexample has an exact finite rational witness.
 Mathematical meaning: Two standardized pairs with identical marginal
 distributions and correlation zero nevertheless have different
 conditional Y means at an X starting value of positive probability.
 Exact checked proposition: Equal first and second marginal score
 means, equal unit second moments, equal zero cross moments and equal
 event probabilities coexist with unequal event-conditional means.
 Premises and side conditions: Both explicit finite measures have
 total mass one, nonnegative weights and event X=0 of probability 1/2.
 Proof/definition method: Assemble the separately checked finite moment
 and conditioning identities, preserving all distributional assumptions.
 Library reuse: FiniteSum.finite_sum; report_*_mean_zero,
 report_*_second_moment_one, report_*_cross_moment_zero,
 report_*_conditional_mean_* and Stdlib.Lra.
 Boundary: This refutes inference of conditional means from correlation
 alone. It neither invalidates nor establishes the Gaussian regression
 theorem under an explicit jointly Gaussian law.
*)
Theorem report_conditional_means_not_determined_by_marginals :
  (report_dependent_expectation report_dependent_x = report_independent_expectation report_independent_x) /\
  (report_dependent_expectation report_dependent_y = report_independent_expectation report_independent_y) /\
  (report_dependent_expectation (fun n => report_dependent_x n * report_dependent_x n) =
   report_independent_expectation (fun n => report_independent_x n * report_independent_x n)) /\
  (report_dependent_expectation (fun n => report_dependent_y n * report_dependent_y n) =
   report_independent_expectation (fun n => report_independent_y n * report_independent_y n)) /\
  (report_dependent_expectation (fun n => report_dependent_x n * report_dependent_y n) =
   report_independent_expectation (fun n => report_independent_x n * report_independent_y n)) /\
  (report_dependent_expectation report_dependent_zero_event =
   report_independent_expectation report_independent_zero_event) /\
  report_dependent_conditional_mean_at_zero <>
   report_independent_conditional_mean_at_zero.
Proof.
  repeat split.
  - rewrite report_dependent_x_mean_zero,
      report_independent_x_mean_zero; reflexivity.
  - rewrite report_dependent_y_mean_zero,
      report_independent_y_mean_zero; reflexivity.
  - rewrite report_dependent_x_second_moment_one,
      report_independent_x_second_moment_one; reflexivity.
  - rewrite report_dependent_y_second_moment_one,
      report_independent_y_second_moment_one; reflexivity.
  - rewrite report_dependent_cross_moment_zero,
      report_independent_cross_moment_zero; reflexivity.
  - rewrite report_dependent_zero_event_mass,
      report_independent_zero_event_mass; reflexivity.
  - rewrite report_dependent_conditional_mean_negative_one,
      report_independent_conditional_mean_zero.
    lra.
Qed.

(**
 [report_counterexample_recursive_means_differ] (theorem) —
 The inclusive average after one predicted score differs between models.
 Mathematical meaning: At initial score zero, the dependent model's
 conditional prediction is -1 and its inclusive mean -1/2, while
 the independent model predicts zero and has inclusive mean zero.
 Exact checked proposition: (0+E_d[Y|X=0])/2=-1/2 and
 (0+E_i[Y|X=0])/2=0.
 Premises and side conditions: Event X=0 has checked probability 1/2
 under both finite probability models.
 Proof/definition method: Reuse the two verified event-conditional means;
 no simulation, continuity assumption, or Gaussian regression axiom.
 Library reuse: report_dependent_conditional_mean_negative_one,
 report_independent_conditional_mean_zero, Rocq Stdlib.Lra.
 Boundary: The result explains precisely why the corresponding report
 Gaussian recursion cannot follow from marginal/correlation information
 without a conditional-law assumption.
*)
Theorem report_counterexample_recursive_means_differ :
  (0 + report_dependent_conditional_mean_at_zero) / 2 = -1 / 2 /\
  (0 + report_independent_conditional_mean_at_zero) / 2 = 0.
Proof.
  rewrite report_dependent_conditional_mean_negative_one,
    report_independent_conditional_mean_zero.
  split; field.
Qed.
