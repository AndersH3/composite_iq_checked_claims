(** Module: FourContrastCovariance.v
 Purpose: Supply exact four-test covariance and variance formulas for
 linear composites, paired contrasts and partial sequential test histories
 across the six Hoeflin/Ferguson, Towers and Sequential report volumes.
 Mathematical representation: A symmetric symbolic 4x4 covariance matrix
 with ten independent entries and bilinear contraction, not a new
 summation, probability, Gaussian distribution or population model.
 Explicit hypotheses: Symbolic covariance entries and score coefficients
 are arbitrary real numbers; positivity and PSD must not be inferred
 without a separately stated covariance feasibility premise.
 Library use: Rocq Stdlib Reals, Ring and Psatz; all polynomial identities
 are reduced by the maintained ring tactic, not a custom algebra system.
 The existing ListPoolingAlgebra is the canonical finite-sample owner.
 Limitations: Entries must be provided by a valid covariance construction
 in statistical applications. No stochastic Gaussian conditioning,
 binomial trial law, coverage probability or empirical IQ model is proved.
 Reproduction: scripts/check_rocq_documentation.sh and
 scripts/compile_rocq.sh under pinned Rocq 9.2 GitHub Actions.
 AI disclosure: OpenAI ChatGPT assisted specification, source creation,
 algebraic validation and reporting. Rocq kernel checks are authoritative.
*)
From Stdlib Require Import Reals Ring Field.
Require Import FiniteSum ListPoolingAlgebra.
Open Scope R_scope.

(** [four_covariant] (definition).
 Mathematical meaning: Symmetric bilinear covariance form for four test-score coefficients and ten distinct covariance matrix entries.
 Exact declaration: four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4.
 Premises and side conditions: All covariance entries are arbitrary real scalars, so the formula by itself does not assume a positive semidefinite matrix, a Gaussian random vector or independent observations.
 Proof/definition method: Each diagonal entry contributes one coefficient product and each off-diagonal entry contributes the two symmetric cross-products; this is a direct nonrecursive polynomial definition.
 Library reuse: Rocq Stdlib Reals/Ring, and the established canonical finite-sum/sample covariance library for any future realization.
 Boundary: Deterministic bilinear matrix contraction only; covariance feasibility and Gaussian distributions remain separate.
*)
Definition four_covariant
 (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R)
 (a1 a2 a3 a4 b1 b2 b3 b4:R) : R :=
 a1*b1*s11 + a2*b2*s22 + a3*b3*s33 + a4*b4*s44
 + (a1*b2+a2*b1)*s12 + (a1*b3+a3*b1)*s13
 + (a1*b4+a4*b1)*s14 + (a2*b3+a3*b2)*s23
 + (a2*b4+a4*b2)*s24 + (a3*b4+a4*b3)*s34.

(** [four_quadratic] (definition).
 Mathematical meaning: Quadratic variance expression for one four-test linear composite, derived from the single shared bilinear covariance form.
 Exact declaration: four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4.
 Premises and side conditions: A real expression only; nonnegative variance requires an actual positive semidefinite covariance matrix, not asserted here.
 Proof/definition method: Self-application of four_covariant; retains one source of covariance sign and coefficient conventions.
 Library reuse: The already defined four_covariant and Rocq Stdlib Reals/Ring rather than a second hand-expanded quadratic implementation.
 Boundary: Deterministic G01 covariance-composite algebra, no Gaussian conditional law or population estimate.
*)
Definition four_quadratic
 (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4:R) : R :=
 four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 a1 a2 a3 a4.

(** [four_covariant_symmetry] (theorem).
 Mathematical meaning: Swapping two four-test composite scores leaves their symmetric covariance unchanged.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4 = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 a1 a2 a3 a4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_symmetry :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4 = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 a1 a2 a3 a4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_quadratic_double_cross] (theorem).
 Mathematical meaning: The variance of the sum of two composites is the sum of their variances plus twice their covariance.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1+b1) (a2+b2) (a3+b3) (a4+b4) = four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 + four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 + 2*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_quadratic_double_cross :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1+b1) (a2+b2) (a3+b3) (a4+b4) = four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 + four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 + 2*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_quadratic_difference] (theorem).
 Mathematical meaning: The variance of the difference of two composites subtracts twice their covariance from the sum of variances.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1-b1) (a2-b2) (a3-b3) (a4-b4) = four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 + four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 - 2*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_quadratic_difference :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1-b1) (a2-b2) (a3-b3) (a4-b4) = four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 + four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 - 2*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_scale_left] (theorem).
 Mathematical meaning: Rescaling the first composite scales its covariance with a second composite by the same factor.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (k:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (k*a1) (k*a2) (k*a3) (k*a4) b1 b2 b3 b4 = k*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_scale_left :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (k:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (k*a1) (k*a2) (k*a3) (k*a4) b1 b2 b3 b4 = k*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_scale_right] (theorem).
 Mathematical meaning: Rescaling the second composite scales covariance by the same factor.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (k:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 (k*b1) (k*b2) (k*b3) (k*b4) = k*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_scale_right :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (k:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 (k*b1) (k*b2) (k*b3) (k*b4) = k*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_scale_both] (theorem).
 Mathematical meaning: A common scaling of both composites multiplies covariance by the squared scaling factor.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (k:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (k*a1) (k*a2) (k*a3) (k*a4) (k*b1) (k*b2) (k*b3) (k*b4) = k*k*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_scale_both :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (k:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (k*a1) (k*a2) (k*a3) (k*a4) (k*b1) (k*b2) (k*b3) (k*b4) = k*k*four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_quadratic_scale] (theorem).
 Mathematical meaning: A rescaled four-test composite has variance scaling quadratically with its score coefficients.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 k:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (k*a1) (k*a2) (k*a3) (k*a4) = k*k*four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_quadratic_scale :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 k:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (k*a1) (k*a2) (k*a3) (k*a4) = k*k*four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_add_left] (theorem).
 Mathematical meaning: Covariance is additive in two composite-score coefficient vectors on its left.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1+b1) (a2+b2) (a3+b3) (a4+b4) c1 c2 c3 c4 = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4 + four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 c1 c2 c3 c4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_add_left :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1+b1) (a2+b2) (a3+b3) (a4+b4) c1 c2 c3 c4 = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4 + four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 c1 c2 c3 c4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_add_right] (theorem).
 Mathematical meaning: Covariance is additive in two composite-score coefficient vectors on its right.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 (b1+c1) (b2+c2) (b3+c3) (b4+c4) = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4 + four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_add_right :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 (b1+c1) (b2+c2) (b3+c3) (b4+c4) = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4 + four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_sub_left] (theorem).
 Mathematical meaning: Subtracting a composite on the left subtracts its covariance contribution.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1-b1) (a2-b2) (a3-b3) (a4-b4) c1 c2 c3 c4 = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4 - four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 c1 c2 c3 c4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_sub_left :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 (a1-b1) (a2-b2) (a3-b3) (a4-b4) c1 c2 c3 c4 = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4 - four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 b1 b2 b3 b4 c1 c2 c3 c4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_sub_right] (theorem).
 Mathematical meaning: Subtracting a composite on the right subtracts its covariance contribution.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 (b1-c1) (b2-c2) (b3-c3) (b4-c4) = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4 - four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_sub_right :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4 b1 b2 b3 b4:R) (c1 c2 c3 c4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 (b1-c1) (b2-c2) (b3-c3) (b4-c4) = four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 b1 b2 b3 b4 - four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 c1 c2 c3 c4.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_quadratic_zero_contrast] (theorem).
 Mathematical meaning: The all-zero score contrast has identically zero variance for any symmetric covariance symbols.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 0 = 0
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_quadratic_zero_contrast :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_quadratic s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 0 = 0.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_zero_left] (theorem).
 Mathematical meaning: An all-zero first score contrast has zero covariance with every second contrast.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (b1 b2 b3 b4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 0 b1 b2 b3 b4 = 0
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_zero_left :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (b1 b2 b3 b4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 0 b1 b2 b3 b4 = 0.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_covariant_zero_right] (theorem).
 Mathematical meaning: An all-zero second score contrast has zero covariance with every first contrast.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 0 0 0 0 = 0
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_covariant_zero_right :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R) (a1 a2 a3 a4:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 a1 a2 a3 a4 0 0 0 0 = 0.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_test1] (theorem).
 Mathematical meaning: For the test 1 alone and the test 1 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 0 0 = s11
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_test1 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 0 0 = s11.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_test2] (theorem).
 Mathematical meaning: For the test 1 alone and the test 2 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 0 0 = s12
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_test2 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 0 0 = s12.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_test3] (theorem).
 Mathematical meaning: For the test 1 alone and the test 3 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 0 1 0 = s13
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_test3 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 0 1 0 = s13.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_test4] (theorem).
 Mathematical meaning: For the test 1 alone and the test 4 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 0 0 1 = s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_test4 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 0 0 1 = s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_difference12] (theorem).
 Mathematical meaning: For the test 1 alone and the test 1 minus test 2, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 (-1) 0 0 = s11 - s12
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_difference12 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 (-1) 0 0 = s11 - s12.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_difference13] (theorem).
 Mathematical meaning: For the test 1 alone and the test 1 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 (-1) 0 = s11 - s13
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_difference13 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 (-1) 0 = s11 - s13.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_difference14] (theorem).
 Mathematical meaning: For the test 1 alone and the test 1 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 0 (-1) = s11 - s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_difference14 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 0 (-1) = s11 - s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_difference23] (theorem).
 Mathematical meaning: For the test 1 alone and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 (-1) 0 = s12 - s13
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 (-1) 0 = s12 - s13.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_difference24] (theorem).
 Mathematical meaning: For the test 1 alone and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 0 (-1) = s12 - s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 0 (-1) = s12 - s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_difference34] (theorem).
 Mathematical meaning: For the test 1 alone and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 0 1 (-1) = s13 - s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 0 1 (-1) = s13 - s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_triple123] (theorem).
 Mathematical meaning: For the test 1 alone and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 1 0 = s11 + s12 + s13
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 1 0 = s11 + s12 + s13.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_triple124] (theorem).
 Mathematical meaning: For the test 1 alone and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 0 1 = s11 + s12 + s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 0 1 = s11 + s12 + s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_triple134] (theorem).
 Mathematical meaning: For the test 1 alone and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 1 1 = s11 + s13 + s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 0 1 1 = s11 + s13 + s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_triple234] (theorem).
 Mathematical meaning: For the test 1 alone and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 1 1 = s12 + s13 + s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 0 1 1 1 = s12 + s13 + s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_allfour] (theorem).
 Mathematical meaning: For the test 1 alone and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 1 1 = s11 + s12 + s13 + s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 1 1 = s11 + s12 + s13 + s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test1_balanced12v34] (theorem).
 Mathematical meaning: For the test 1 alone and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 (-1) (-1) = s11 + s12 - s13 - s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test1_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 0 1 1 (-1) (-1) = s11 + s12 - s13 - s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_test2] (theorem).
 Mathematical meaning: For the test 2 alone and the test 2 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 0 0 = s22
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_test2 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 0 0 = s22.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_test3] (theorem).
 Mathematical meaning: For the test 2 alone and the test 3 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 0 1 0 = s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_test3 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 0 1 0 = s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_test4] (theorem).
 Mathematical meaning: For the test 2 alone and the test 4 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 0 0 1 = s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_test4 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 0 0 1 = s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_difference12] (theorem).
 Mathematical meaning: For the test 2 alone and the test 1 minus test 2, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 (-1) 0 0 = - s22 + s12
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_difference12 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 (-1) 0 0 = - s22 + s12.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_difference13] (theorem).
 Mathematical meaning: For the test 2 alone and the test 1 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 0 (-1) 0 = s12 - s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_difference13 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 0 (-1) 0 = s12 - s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_difference14] (theorem).
 Mathematical meaning: For the test 2 alone and the test 1 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 0 0 (-1) = s12 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_difference14 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 0 0 (-1) = s12 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_difference23] (theorem).
 Mathematical meaning: For the test 2 alone and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 (-1) 0 = s22 - s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 (-1) 0 = s22 - s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_difference24] (theorem).
 Mathematical meaning: For the test 2 alone and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 0 (-1) = s22 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 0 (-1) = s22 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_difference34] (theorem).
 Mathematical meaning: For the test 2 alone and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 0 1 (-1) = s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 0 1 (-1) = s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_triple123] (theorem).
 Mathematical meaning: For the test 2 alone and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 1 0 = s22 + s12 + s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 1 0 = s22 + s12 + s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_triple124] (theorem).
 Mathematical meaning: For the test 2 alone and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 0 1 = s22 + s12 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 0 1 = s22 + s12 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_triple134] (theorem).
 Mathematical meaning: For the test 2 alone and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 0 1 1 = s12 + s23 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 0 1 1 = s12 + s23 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_triple234] (theorem).
 Mathematical meaning: For the test 2 alone and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 1 1 = s22 + s23 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 0 1 1 1 = s22 + s23 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_allfour] (theorem).
 Mathematical meaning: For the test 2 alone and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 1 1 = s22 + s12 + s23 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 1 1 = s22 + s12 + s23 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test2_balanced12v34] (theorem).
 Mathematical meaning: For the test 2 alone and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 (-1) (-1) = s22 + s12 - s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test2_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 0 1 1 (-1) (-1) = s22 + s12 - s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_test3] (theorem).
 Mathematical meaning: For the test 3 alone and the test 3 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 0 1 0 = s33
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_test3 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 0 1 0 = s33.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_test4] (theorem).
 Mathematical meaning: For the test 3 alone and the test 4 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 0 0 1 = s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_test4 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 0 0 1 = s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_difference12] (theorem).
 Mathematical meaning: For the test 3 alone and the test 1 minus test 2, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 (-1) 0 0 = s13 - s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_difference12 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 (-1) 0 0 = s13 - s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_difference13] (theorem).
 Mathematical meaning: For the test 3 alone and the test 1 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 0 (-1) 0 = - s33 + s13
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_difference13 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 0 (-1) 0 = - s33 + s13.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_difference14] (theorem).
 Mathematical meaning: For the test 3 alone and the test 1 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 0 0 (-1) = s13 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_difference14 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 0 0 (-1) = s13 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_difference23] (theorem).
 Mathematical meaning: For the test 3 alone and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 1 (-1) 0 = - s33 + s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 1 (-1) 0 = - s33 + s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_difference24] (theorem).
 Mathematical meaning: For the test 3 alone and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 1 0 (-1) = s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 1 0 (-1) = s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_difference34] (theorem).
 Mathematical meaning: For the test 3 alone and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 0 1 (-1) = s33 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 0 1 (-1) = s33 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_triple123] (theorem).
 Mathematical meaning: For the test 3 alone and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 1 0 = s33 + s13 + s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 1 0 = s33 + s13 + s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_triple124] (theorem).
 Mathematical meaning: For the test 3 alone and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 0 1 = s13 + s23 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 0 1 = s13 + s23 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_triple134] (theorem).
 Mathematical meaning: For the test 3 alone and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 0 1 1 = s33 + s13 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 0 1 1 = s33 + s13 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_triple234] (theorem).
 Mathematical meaning: For the test 3 alone and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 1 1 1 = s33 + s23 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 0 1 1 1 = s33 + s23 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_allfour] (theorem).
 Mathematical meaning: For the test 3 alone and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 1 1 = s33 + s13 + s23 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 1 1 = s33 + s13 + s23 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test3_balanced12v34] (theorem).
 Mathematical meaning: For the test 3 alone and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 (-1) (-1) = - s33 + s13 + s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test3_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 0 1 1 (-1) (-1) = - s33 + s13 + s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_test4] (theorem).
 Mathematical meaning: For the test 4 alone and the test 4 alone, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 0 0 1 = s44
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_test4 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 0 0 1 = s44.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_difference12] (theorem).
 Mathematical meaning: For the test 4 alone and the test 1 minus test 2, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 (-1) 0 0 = s14 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_difference12 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 (-1) 0 0 = s14 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_difference13] (theorem).
 Mathematical meaning: For the test 4 alone and the test 1 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 0 (-1) 0 = s14 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_difference13 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 0 (-1) 0 = s14 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_difference14] (theorem).
 Mathematical meaning: For the test 4 alone and the test 1 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 0 0 (-1) = - s44 + s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_difference14 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 0 0 (-1) = - s44 + s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_difference23] (theorem).
 Mathematical meaning: For the test 4 alone and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 1 (-1) 0 = s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 1 (-1) 0 = s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_difference24] (theorem).
 Mathematical meaning: For the test 4 alone and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 1 0 (-1) = - s44 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 1 0 (-1) = - s44 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_difference34] (theorem).
 Mathematical meaning: For the test 4 alone and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 0 1 (-1) = - s44 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 0 1 (-1) = - s44 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_triple123] (theorem).
 Mathematical meaning: For the test 4 alone and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 1 0 = s14 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 1 0 = s14 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_triple124] (theorem).
 Mathematical meaning: For the test 4 alone and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 0 1 = s44 + s14 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 0 1 = s44 + s14 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_triple134] (theorem).
 Mathematical meaning: For the test 4 alone and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 0 1 1 = s44 + s14 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 0 1 1 = s44 + s14 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_triple234] (theorem).
 Mathematical meaning: For the test 4 alone and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 1 1 1 = s44 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 0 1 1 1 = s44 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_allfour] (theorem).
 Mathematical meaning: For the test 4 alone and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 1 1 = s44 + s14 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 1 1 = s44 + s14 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_test4_balanced12v34] (theorem).
 Mathematical meaning: For the test 4 alone and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 (-1) (-1) = - s44 + s14 + s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_test4_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 0 1 1 1 (-1) (-1) = - s44 + s14 + s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_difference12] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the test 1 minus test 2, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 (-1) 0 0 = s11 + s22 - 2*s12
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_difference12 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 (-1) 0 0 = s11 + s22 - 2*s12.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_difference13] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the test 1 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 0 (-1) 0 = s11 - s12 - s13 + s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_difference13 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 0 (-1) 0 = s11 - s12 - s13 + s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_difference14] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the test 1 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 0 0 (-1) = s11 - s12 - s14 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_difference14 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 0 0 (-1) = s11 - s12 - s14 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_difference23] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 1 (-1) 0 = - s22 + s12 - s13 + s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 1 (-1) 0 = - s22 + s12 - s13 + s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_difference24] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 1 0 (-1) = - s22 + s12 - s14 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 1 0 (-1) = - s22 + s12 - s14 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_difference34] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 0 1 (-1) = s13 - s14 - s23 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 0 1 (-1) = s13 - s14 - s23 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_triple123] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 1 0 = s11 - s22 + s13 - s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 1 0 = s11 - s22 + s13 - s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_triple124] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 0 1 = s11 - s22 + s14 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 0 1 = s11 - s22 + s14 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_triple134] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 0 1 1 = s11 - s12 + s13 + s14 - s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 0 1 1 = s11 - s12 + s13 + s14 - s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_triple234] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 1 1 1 = - s22 + s12 + s13 + s14 - s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 0 1 1 1 = - s22 + s12 + s13 + s14 - s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_allfour] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 1 1 = s11 - s22 + s13 + s14 - s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 1 1 = s11 - s22 + s13 + s14 - s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference12_balanced12v34] (theorem).
 Mathematical meaning: For the test 1 minus test 2 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 (-1) (-1) = s11 - s22 - s13 - s14 + s23 + s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference12_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 (-1) 0 0 1 1 (-1) (-1) = s11 - s22 - s13 - s14 + s23 + s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_difference13] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the test 1 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 0 (-1) 0 = s11 + s33 - 2*s13
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_difference13 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 0 (-1) 0 = s11 + s33 - 2*s13.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_difference14] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the test 1 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 0 0 (-1) = s11 - s13 - s14 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_difference14 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 0 0 (-1) = s11 - s13 - s14 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_difference23] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 1 (-1) 0 = s33 + s12 - s13 - s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 1 (-1) 0 = s33 + s12 - s13 - s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_difference24] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 1 0 (-1) = s12 - s14 - s23 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 1 0 (-1) = s12 - s14 - s23 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_difference34] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 0 1 (-1) = - s33 + s13 - s14 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 0 1 (-1) = - s33 + s13 - s14 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_triple123] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 1 0 = s11 - s33 + s12 - s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 1 0 = s11 - s33 + s12 - s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_triple124] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 0 1 = s11 + s12 - s13 + s14 - s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 0 1 = s11 + s12 - s13 + s14 - s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_triple134] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 0 1 1 = s11 - s33 + s14 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 0 1 1 = s11 - s33 + s14 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_triple234] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 1 1 1 = - s33 + s12 + s13 + s14 - s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 0 1 1 1 = - s33 + s12 + s13 + s14 - s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_allfour] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 1 1 = s11 - s33 + s12 + s14 - s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 1 1 = s11 - s33 + s12 + s14 - s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference13_balanced12v34] (theorem).
 Mathematical meaning: For the test 1 minus test 3 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 (-1) (-1) = s11 + s33 + s12 - 2*s13 - s14 - s23 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference13_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 (-1) 0 1 1 (-1) (-1) = s11 + s33 + s12 - 2*s13 - s14 - s23 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_difference14] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the test 1 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 0 0 (-1) = s11 + s44 - 2*s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_difference14 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 0 0 (-1) = s11 + s44 - 2*s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_difference23] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 1 (-1) 0 = s12 - s13 - s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 1 (-1) 0 = s12 - s13 - s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_difference24] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 1 0 (-1) = s44 + s12 - s14 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 1 0 (-1) = s44 + s12 - s14 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_difference34] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 0 1 (-1) = s44 + s13 - s14 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 0 1 (-1) = s44 + s13 - s14 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_triple123] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 1 0 = s11 + s12 + s13 - s14 - s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 1 0 = s11 + s12 + s13 - s14 - s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_triple124] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 0 1 = s11 - s44 + s12 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 0 1 = s11 - s44 + s12 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_triple134] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 0 1 1 = s11 - s44 + s13 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 0 1 1 = s11 - s44 + s13 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_triple234] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 1 1 1 = - s44 + s12 + s13 + s14 - s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 0 1 1 1 = - s44 + s12 + s13 + s14 - s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_allfour] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 1 1 = s11 - s44 + s12 + s13 - s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 1 1 = s11 - s44 + s12 + s13 - s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference14_balanced12v34] (theorem).
 Mathematical meaning: For the test 1 minus test 4 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 (-1) (-1) = s11 + s44 + s12 - s13 - 2*s14 - s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference14_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 0 (-1) 1 1 (-1) (-1) = s11 + s44 + s12 - s13 - 2*s14 - s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_difference23] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the test 2 minus test 3, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 1 (-1) 0 = s22 + s33 - 2*s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_difference23 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 1 (-1) 0 = s22 + s33 - 2*s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_difference24] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 1 0 (-1) = s22 - s23 - s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 1 0 (-1) = s22 - s23 - s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_difference34] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 0 1 (-1) = - s33 + s23 - s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 0 1 (-1) = - s33 + s23 - s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_triple123] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 1 0 = s22 - s33 + s12 - s13
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 1 0 = s22 - s33 + s12 - s13.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_triple124] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 0 1 = s22 + s12 - s13 - s23 + s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 0 1 = s22 + s12 - s13 - s23 + s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_triple134] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 0 1 1 = - s33 + s12 - s13 + s23 + s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 0 1 1 = - s33 + s12 - s13 + s23 + s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_triple234] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 1 1 1 = s22 - s33 + s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 0 1 1 1 = s22 - s33 + s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_allfour] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 1 1 = s22 - s33 + s12 - s13 + s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 1 1 = s22 - s33 + s12 - s13 + s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference23_balanced12v34] (theorem).
 Mathematical meaning: For the test 2 minus test 3 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 (-1) (-1) = s22 + s33 + s12 - s13 - 2*s23 - s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference23_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 (-1) 0 1 1 (-1) (-1) = s22 + s33 + s12 - s13 - 2*s23 - s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_difference24] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the test 2 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 0 1 0 (-1) = s22 + s44 - 2*s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_difference24 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 0 1 0 (-1) = s22 + s44 - 2*s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_difference34] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 0 0 1 (-1) = s44 + s23 - s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 0 0 1 (-1) = s44 + s23 - s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_triple123] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 1 0 = s22 + s12 - s14 + s23 - s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 1 0 = s22 + s12 - s14 + s23 - s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_triple124] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 0 1 = s22 - s44 + s12 - s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 0 1 = s22 - s44 + s12 - s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_triple134] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 0 1 1 = - s44 + s12 - s14 + s23 + s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 0 1 1 = - s44 + s12 - s14 + s23 + s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_triple234] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 0 1 1 1 = s22 - s44 + s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 0 1 1 1 = s22 - s44 + s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_allfour] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 1 1 = s22 - s44 + s12 - s14 + s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 1 1 = s22 - s44 + s12 - s14 + s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference24_balanced12v34] (theorem).
 Mathematical meaning: For the test 2 minus test 4 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 (-1) (-1) = s22 + s44 + s12 - s14 - s23 - 2*s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference24_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 0 (-1) 1 1 (-1) (-1) = s22 + s44 + s12 - s14 - s23 - 2*s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference34_difference34] (theorem).
 Mathematical meaning: For the test 3 minus test 4 and the test 3 minus test 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 0 0 1 (-1) = s33 + s44 - 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference34_difference34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 0 0 1 (-1) = s33 + s44 - 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference34_triple123] (theorem).
 Mathematical meaning: For the test 3 minus test 4 and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 1 0 = s33 + s13 - s14 + s23 - s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference34_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 1 0 = s33 + s13 - s14 + s23 - s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference34_triple124] (theorem).
 Mathematical meaning: For the test 3 minus test 4 and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 0 1 = - s44 + s13 - s14 + s23 - s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference34_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 0 1 = - s44 + s13 - s14 + s23 - s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference34_triple134] (theorem).
 Mathematical meaning: For the test 3 minus test 4 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 0 1 1 = s33 - s44 + s13 - s14
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference34_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 0 1 1 = s33 - s44 + s13 - s14.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference34_triple234] (theorem).
 Mathematical meaning: For the test 3 minus test 4 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 0 1 1 1 = s33 - s44 + s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference34_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 0 1 1 1 = s33 - s44 + s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference34_allfour] (theorem).
 Mathematical meaning: For the test 3 minus test 4 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 1 1 = s33 - s44 + s13 - s14 + s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference34_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 1 1 = s33 - s44 + s13 - s14 + s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_difference34_balanced12v34] (theorem).
 Mathematical meaning: For the test 3 minus test 4 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 (-1) (-1) = - s33 + s44 + s13 - s14 + s23 - s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_difference34_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 0 1 (-1) 1 1 (-1) (-1) = - s33 + s44 + s13 - s14 + s23 - s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple123_triple123] (theorem).
 Mathematical meaning: For the sum of the first three tests and the sum of the first three tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 1 0 = s11 + s22 + s33 + 2*s12 + 2*s13 + 2*s23
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple123_triple123 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 1 0 = s11 + s22 + s33 + 2*s12 + 2*s13 + 2*s23.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple123_triple124] (theorem).
 Mathematical meaning: For the sum of the first three tests and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 0 1 = s11 + s22 + 2*s12 + s13 + s14 + s23 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple123_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 0 1 = s11 + s22 + 2*s12 + s13 + s14 + s23 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple123_triple134] (theorem).
 Mathematical meaning: For the sum of the first three tests and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 0 1 1 = s11 + s33 + s12 + 2*s13 + s14 + s23 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple123_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 0 1 1 = s11 + s33 + s12 + 2*s13 + s14 + s23 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple123_triple234] (theorem).
 Mathematical meaning: For the sum of the first three tests and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 0 1 1 1 = s22 + s33 + s12 + s13 + s14 + 2*s23 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple123_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 0 1 1 1 = s22 + s33 + s12 + s13 + s14 + 2*s23 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple123_allfour] (theorem).
 Mathematical meaning: For the sum of the first three tests and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 1 1 = s11 + s22 + s33 + 2*s12 + 2*s13 + s14 + 2*s23 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple123_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 1 1 = s11 + s22 + s33 + 2*s12 + 2*s13 + s14 + 2*s23 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple123_balanced12v34] (theorem).
 Mathematical meaning: For the sum of the first three tests and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 (-1) (-1) = s11 + s22 - s33 + 2*s12 - s14 - s24 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple123_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 0 1 1 (-1) (-1) = s11 + s22 - s33 + 2*s12 - s14 - s24 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple124_triple124] (theorem).
 Mathematical meaning: For the sum of tests 1, 2 and 4 and the sum of tests 1, 2 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 1 0 1 = s11 + s22 + s44 + 2*s12 + 2*s14 + 2*s24
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple124_triple124 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 1 0 1 = s11 + s22 + s44 + 2*s12 + 2*s14 + 2*s24.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple124_triple134] (theorem).
 Mathematical meaning: For the sum of tests 1, 2 and 4 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 0 1 1 = s11 + s44 + s12 + s13 + 2*s14 + s23 + s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple124_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 0 1 1 = s11 + s44 + s12 + s13 + 2*s14 + s23 + s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple124_triple234] (theorem).
 Mathematical meaning: For the sum of tests 1, 2 and 4 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 0 1 1 1 = s22 + s44 + s12 + s13 + s14 + s23 + 2*s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple124_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 0 1 1 1 = s22 + s44 + s12 + s13 + s14 + s23 + 2*s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple124_allfour] (theorem).
 Mathematical meaning: For the sum of tests 1, 2 and 4 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 1 1 1 = s11 + s22 + s44 + 2*s12 + s13 + 2*s14 + s23 + 2*s24 + s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple124_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 1 1 1 = s11 + s22 + s44 + 2*s12 + s13 + 2*s14 + s23 + 2*s24 + s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple124_balanced12v34] (theorem).
 Mathematical meaning: For the sum of tests 1, 2 and 4 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 1 (-1) (-1) = s11 + s22 - s44 + 2*s12 - s13 - s23 - s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple124_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 0 1 1 1 (-1) (-1) = s11 + s22 - s44 + 2*s12 - s13 - s23 - s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple134_triple134] (theorem).
 Mathematical meaning: For the sum of tests 1, 3 and 4 and the sum of tests 1, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 1 0 1 1 = s11 + s33 + s44 + 2*s13 + 2*s14 + 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple134_triple134 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 1 0 1 1 = s11 + s33 + s44 + 2*s13 + 2*s14 + 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple134_triple234] (theorem).
 Mathematical meaning: For the sum of tests 1, 3 and 4 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 0 1 1 1 = s33 + s44 + s12 + s13 + s14 + s23 + s24 + 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple134_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 0 1 1 1 = s33 + s44 + s12 + s13 + s14 + s23 + s24 + 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple134_allfour] (theorem).
 Mathematical meaning: For the sum of tests 1, 3 and 4 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 1 1 1 1 = s11 + s33 + s44 + s12 + 2*s13 + 2*s14 + s23 + s24 + 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple134_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 1 1 1 1 = s11 + s33 + s44 + s12 + 2*s13 + 2*s14 + s23 + s24 + 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple134_balanced12v34] (theorem).
 Mathematical meaning: For the sum of tests 1, 3 and 4 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 1 1 (-1) (-1) = s11 - s33 - s44 + s12 + s23 + s24 - 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple134_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 0 1 1 1 1 (-1) (-1) = s11 - s33 - s44 + s12 + s23 + s24 - 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple234_triple234] (theorem).
 Mathematical meaning: For the sum of tests 2, 3 and 4 and the sum of tests 2, 3 and 4, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 1 1 0 1 1 1 = s22 + s33 + s44 + 2*s23 + 2*s24 + 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple234_triple234 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 1 1 0 1 1 1 = s22 + s33 + s44 + 2*s23 + 2*s24 + 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple234_allfour] (theorem).
 Mathematical meaning: For the sum of tests 2, 3 and 4 and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 1 1 1 1 1 1 = s22 + s33 + s44 + s12 + s13 + s14 + 2*s23 + 2*s24 + 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple234_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 1 1 1 1 1 1 = s22 + s33 + s44 + s12 + s13 + s14 + 2*s23 + 2*s24 + 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_triple234_balanced12v34] (theorem).
 Mathematical meaning: For the sum of tests 2, 3 and 4 and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 1 1 1 1 (-1) (-1) = s22 - s33 - s44 + s12 + s13 + s14 - 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_triple234_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 0 1 1 1 1 1 (-1) (-1) = s22 - s33 - s44 + s12 + s13 + s14 - 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_allfour_allfour] (theorem).
 Mathematical meaning: For the total of all four tests and the total of all four tests, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 1 1 1 1 1 = s11 + s22 + s33 + s44 + 2*s12 + 2*s13 + 2*s14 + 2*s23 + 2*s24 + 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_allfour_allfour :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 1 1 1 1 1 = s11 + s22 + s33 + s44 + 2*s12 + 2*s13 + 2*s14 + 2*s23 + 2*s24 + 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_allfour_balanced12v34] (theorem).
 Mathematical meaning: For the total of all four tests and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 1 1 1 (-1) (-1) = s11 + s22 - s33 - s44 + 2*s12 - 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_allfour_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 1 1 1 1 (-1) (-1) = s11 + s22 - s33 - s44 + 2*s12 - 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.

(** [four_contrast_cov_balanced12v34_balanced12v34] (theorem).
 Mathematical meaning: For the first-pair versus second-pair score contrast and the first-pair versus second-pair score contrast, compute the exact covariance coefficient polynomial, identifying precisely which test variances and within/between-test covariances contribute to their composite association.
 Exact checked proposition: forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 (-1) (-1) 1 1 (-1) (-1) = s11 + s22 + s33 + s44 + 2*s12 - 2*s13 - 2*s14 - 2*s23 - 2*s24 + 2*s34
 Premises and side conditions: Ten symmetric covariance symbols and all contrast coefficients are explicit real inputs. No positive-semidefiniteness or statistical sampling model is asserted by an unconditional polynomial identity.
 Proof/definition method: Unfold the shared symmetric bilinear contraction and normalize the exact real polynomial with the maintained Rocq ring tactic.
 Library reuse: Rocq Stdlib Reals and Ring for the sole symmetric four-variable contraction; avoids duplicating finite sums or introducing custom rewrite engines. ListPoolingAlgebra remains the canonical sample-moment source.
 Boundary: Exact deterministic four-test composite algebra for G01 and sequential/test-combination report formulas only; not a Gaussian law, independent sampling certificate or empirical IQ model.
*)
Theorem four_contrast_cov_balanced12v34_balanced12v34 :
  forall (s11 s22 s33 s44 s12 s13 s14 s23 s24 s34:R), four_covariant s11 s22 s33 s44 s12 s13 s14 s23 s24 s34 1 1 (-1) (-1) 1 1 (-1) (-1) = s11 + s22 + s33 + s44 + 2*s12 - 2*s13 - 2*s14 - 2*s23 - 2*s24 + 2*s34.
Proof.
  intros; cbv [four_covariant four_quadratic]; ring.
Qed.


(** Bridge from symbolic four-test contrasts to the existing arbitrary-list
    finite-sample covariance library. No second estimator is defined. *)

(** [four_batch_cross_add_right] (theorem).
 Mathematical meaning: Weighted mixed first moments are linear in the second observed attribute over arbitrary lists of batches.
 Exact checked proposition: forall (A:Type) (w x y z:A->R) (xs:list A), batch_cross w x (fun t => y t+z t) xs = batch_cross w x y xs+batch_cross w x z xs
 Premises and side conditions: Each quantified group is an arbitrary occurrence in a finite list. Nonzero total batch mass is an explicit hypothesis wherever division is required; no independence, normality or positive matrix definiteness is inferred.
 Proof/definition method: Reuse the existing canonical finite_sum and ListPoolingAlgebra cross-moment, covariance symmetry and closed-form theorems; normalize only the remaining finite real polynomial or denominators with Rocq's Ring/Field tactics.
 Library reuse: Rocq Stdlib Reals, Ring and Field, FiniteSum and ListPoolingAlgebra rather than a new summation implementation or second covariance definition.
 Boundary: Certified finite weighted-sample covariance arithmetic for G01 and G12; it is not a stochastic Gaussian conditioning theorem, binomial PMF, confidence-coverage proof or empirical IQ model certificate.
*)
Theorem four_batch_cross_add_right :
  forall (A:Type) (w x y z:A->R) (xs:list A), batch_cross w x (fun t => y t+z t) xs = batch_cross w x y xs+batch_cross w x z xs.
Proof.
  intros A w x y z xs; unfold batch_cross.
  transitivity (finite_sum (fun t => w t*x t*y t+w t*x t*z t) xs).
  - apply finite_sum_ext; intro t; ring.
  - rewrite finite_sum_add; reflexivity.
Qed.

(** [four_batch_covariance_add_right] (theorem).
 Mathematical meaning: The weighted finite-sample covariance of a score with a sum is the sum of its two covariances when total weight is nonzero.
 Exact checked proposition: forall (A:Type) (w x y z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w x (fun t=>y t+z t) xs=batch_covariance w x y xs+batch_covariance w x z xs
 Premises and side conditions: Each quantified group is an arbitrary occurrence in a finite list. Nonzero total batch mass is an explicit hypothesis wherever division is required; no independence, normality or positive matrix definiteness is inferred.
 Proof/definition method: Reuse the existing canonical finite_sum and ListPoolingAlgebra cross-moment, covariance symmetry and closed-form theorems; normalize only the remaining finite real polynomial or denominators with Rocq's Ring/Field tactics.
 Library reuse: Rocq Stdlib Reals, Ring and Field, FiniteSum and ListPoolingAlgebra rather than a new summation implementation or second covariance definition.
 Boundary: Certified finite weighted-sample covariance arithmetic for G01 and G12; it is not a stochastic Gaussian conditioning theorem, binomial PMF, confidence-coverage proof or empirical IQ model certificate.
*)
Theorem four_batch_covariance_add_right :
  forall (A:Type) (w x y z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w x (fun t=>y t+z t) xs=batch_covariance w x y xs+batch_covariance w x z xs.
Proof.
  intros A w x y z xs Hm.
  rewrite !batch_covariance_closed by exact Hm.
  rewrite four_batch_cross_add_right, batch_total_add_values.
  field; exact Hm.
Qed.

(** [four_batch_covariance_add_left] (theorem).
 Mathematical meaning: The weighted finite-sample covariance of a sum with a score is additive in the first score under the same positive-denominator discipline.
 Exact checked proposition: forall (A:Type) (w x y z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w (fun t=>x t+y t) z xs=batch_covariance w x z xs+batch_covariance w y z xs
 Premises and side conditions: Each quantified group is an arbitrary occurrence in a finite list. Nonzero total batch mass is an explicit hypothesis wherever division is required; no independence, normality or positive matrix definiteness is inferred.
 Proof/definition method: Reuse the existing canonical finite_sum and ListPoolingAlgebra cross-moment, covariance symmetry and closed-form theorems; normalize only the remaining finite real polynomial or denominators with Rocq's Ring/Field tactics.
 Library reuse: Rocq Stdlib Reals, Ring and Field, FiniteSum and ListPoolingAlgebra rather than a new summation implementation or second covariance definition.
 Boundary: Certified finite weighted-sample covariance arithmetic for G01 and G12; it is not a stochastic Gaussian conditioning theorem, binomial PMF, confidence-coverage proof or empirical IQ model certificate.
*)
Theorem four_batch_covariance_add_left :
  forall (A:Type) (w x y z:A->R) (xs:list A), batch_mass w xs<>0 -> batch_covariance w (fun t=>x t+y t) z xs=batch_covariance w x z xs+batch_covariance w y z xs.
Proof.
  intros A w x y z xs Hm.
  rewrite (batch_covariance_symmetry A w (fun t=>x t+y t) z xs).
  rewrite (batch_covariance_symmetry A w x z xs).
  rewrite (batch_covariance_symmetry A w y z xs).
  apply four_batch_covariance_add_right; exact Hm.
Qed.

(** [four_batch_covariance_linear_left] (theorem).
 Mathematical meaning: Any weighted linear combination of two observed test scores has covariance equal to the same linear combination of their individual covariances.
 Exact checked proposition: forall (A:Type) (w x y z:A->R) (xs:list A) (a b:R), batch_mass w xs<>0 -> batch_covariance w (fun t=>a*x t+b*y t) z xs=a*batch_covariance w x z xs+b*batch_covariance w y z xs
 Premises and side conditions: Each quantified group is an arbitrary occurrence in a finite list. Nonzero total batch mass is an explicit hypothesis wherever division is required; no independence, normality or positive matrix definiteness is inferred.
 Proof/definition method: Reuse the existing canonical finite_sum and ListPoolingAlgebra cross-moment, covariance symmetry and closed-form theorems; normalize only the remaining finite real polynomial or denominators with Rocq's Ring/Field tactics.
 Library reuse: Rocq Stdlib Reals, Ring and Field, FiniteSum and ListPoolingAlgebra rather than a new summation implementation or second covariance definition.
 Boundary: Certified finite weighted-sample covariance arithmetic for G01 and G12; it is not a stochastic Gaussian conditioning theorem, binomial PMF, confidence-coverage proof or empirical IQ model certificate.
*)
Theorem four_batch_covariance_linear_left :
  forall (A:Type) (w x y z:A->R) (xs:list A) (a b:R), batch_mass w xs<>0 -> batch_covariance w (fun t=>a*x t+b*y t) z xs=a*batch_covariance w x z xs+b*batch_covariance w y z xs.
Proof.
  intros A w x y z xs a b Hm.
  rewrite four_batch_covariance_add_left by exact Hm.
  rewrite !batch_covariance_scale_left by exact Hm.
  reflexivity.
Qed.

(** [four_batch_covariance_linear_right] (theorem).
 Mathematical meaning: Linear covariance response to an arbitrary two-score weighted combination on the right, including signed score coefficients.
 Exact checked proposition: forall (A:Type) (w x y z:A->R) (xs:list A) (a b:R), batch_mass w xs<>0 -> batch_covariance w x (fun t=>a*y t+b*z t) xs=a*batch_covariance w x y xs+b*batch_covariance w x z xs
 Premises and side conditions: Each quantified group is an arbitrary occurrence in a finite list. Nonzero total batch mass is an explicit hypothesis wherever division is required; no independence, normality or positive matrix definiteness is inferred.
 Proof/definition method: Reuse the existing canonical finite_sum and ListPoolingAlgebra cross-moment, covariance symmetry and closed-form theorems; normalize only the remaining finite real polynomial or denominators with Rocq's Ring/Field tactics.
 Library reuse: Rocq Stdlib Reals, Ring and Field, FiniteSum and ListPoolingAlgebra rather than a new summation implementation or second covariance definition.
 Boundary: Certified finite weighted-sample covariance arithmetic for G01 and G12; it is not a stochastic Gaussian conditioning theorem, binomial PMF, confidence-coverage proof or empirical IQ model certificate.
*)
Theorem four_batch_covariance_linear_right :
  forall (A:Type) (w x y z:A->R) (xs:list A) (a b:R), batch_mass w xs<>0 -> batch_covariance w x (fun t=>a*y t+b*z t) xs=a*batch_covariance w x y xs+b*batch_covariance w x z xs.
Proof.
  intros A w x y z xs a b Hm.
  rewrite four_batch_covariance_add_right by exact Hm.
  rewrite !batch_covariance_scale_right by exact Hm.
  reflexivity.
Qed.

(** [four_batch_covariance_linear_two_composites] (theorem).
 Mathematical meaning: The exact four-cross-covariance expansion for the association between two two-test composite scores.
 Exact checked proposition: forall (A:Type) (w x y z u:A->R) (xs:list A) (a b c d:R), batch_mass w xs<>0 -> batch_covariance w (fun t=>a*x t+b*y t) (fun t=>c*z t+d*u t) xs=a*c*batch_covariance w x z xs+a*d*batch_covariance w x u xs+b*c*batch_covariance w y z xs+b*d*batch_covariance w y u xs
 Premises and side conditions: Each quantified group is an arbitrary occurrence in a finite list. Nonzero total batch mass is an explicit hypothesis wherever division is required; no independence, normality or positive matrix definiteness is inferred.
 Proof/definition method: Reuse the existing canonical finite_sum and ListPoolingAlgebra cross-moment, covariance symmetry and closed-form theorems; normalize only the remaining finite real polynomial or denominators with Rocq's Ring/Field tactics.
 Library reuse: Rocq Stdlib Reals, Ring and Field, FiniteSum and ListPoolingAlgebra rather than a new summation implementation or second covariance definition.
 Boundary: Certified finite weighted-sample covariance arithmetic for G01 and G12; it is not a stochastic Gaussian conditioning theorem, binomial PMF, confidence-coverage proof or empirical IQ model certificate.
*)
Theorem four_batch_covariance_linear_two_composites :
  forall (A:Type) (w x y z u:A->R) (xs:list A) (a b c d:R), batch_mass w xs<>0 -> batch_covariance w (fun t=>a*x t+b*y t) (fun t=>c*z t+d*u t) xs=a*c*batch_covariance w x z xs+a*d*batch_covariance w x u xs+b*c*batch_covariance w y z xs+b*d*batch_covariance w y u xs.
Proof.
  intros A w x y z u xs a b c d Hm.
  rewrite four_batch_covariance_linear_left by exact Hm.
  rewrite !four_batch_covariance_linear_right by exact Hm.
  ring.
Qed.

(** [four_batch_variance_sum] (theorem).
 Mathematical meaning: The exact weighted variance of a sum of two test scores includes twice their sample covariance, not merely the sum of variances.
 Exact checked proposition: forall (A:Type) (w x y:A->R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun t=>x t+y t) xs=batch_variance w x xs+batch_variance w y xs+2*batch_covariance w x y xs
 Premises and side conditions: Each quantified group is an arbitrary occurrence in a finite list. Nonzero total batch mass is an explicit hypothesis wherever division is required; no independence, normality or positive matrix definiteness is inferred.
 Proof/definition method: Reuse the existing canonical finite_sum and ListPoolingAlgebra cross-moment, covariance symmetry and closed-form theorems; normalize only the remaining finite real polynomial or denominators with Rocq's Ring/Field tactics.
 Library reuse: Rocq Stdlib Reals, Ring and Field, FiniteSum and ListPoolingAlgebra rather than a new summation implementation or second covariance definition.
 Boundary: Certified finite weighted-sample covariance arithmetic for G01 and G12; it is not a stochastic Gaussian conditioning theorem, binomial PMF, confidence-coverage proof or empirical IQ model certificate.
*)
Theorem four_batch_variance_sum :
  forall (A:Type) (w x y:A->R) (xs:list A), batch_mass w xs<>0 -> batch_variance w (fun t=>x t+y t) xs=batch_variance w x xs+batch_variance w y xs+2*batch_covariance w x y xs.
Proof.
  intros A w x y xs Hm.
  rewrite <- (batch_covariance_self_variance A w (fun t=>x t+y t) xs).
  rewrite four_batch_covariance_add_left by exact Hm.
  rewrite !four_batch_covariance_add_right by exact Hm.
  rewrite (batch_covariance_symmetry A w y x xs).
  rewrite (batch_covariance_self_variance A w x xs).
  rewrite (batch_covariance_self_variance A w y xs).
  ring.
Qed.


(** [four_batch_score] (definition).
 Mathematical meaning: Build a linear four-score composite pointwise from four observed batch attributes; retain explicit grouping for the two-pair covariance bridge.
 Exact declaration: forall (A:Type), (A->R)^4 inputs and four real coefficients determine one A->R output.
 Premises and side conditions: The four input observations and arbitrary finite batch identifiers are exact real-valued functions. Total sample exposure must be nonzero for a quotient-level covariance identity. Symbolic covariance entries are instantiated by actual sample moment definitions, not unconstrained arbitrary matrix symbols.
 Proof/definition method: Use the standard Rplus/Rmult operations and the existing batch observations, without recursively defining a second moment collector.
 Library reuse: The canonical FiniteSum and ListPoolingAlgebra covariance, variance and linearity theorems are reused directly; Rocq Stdlib Ring/Field handles only real algebra and no new statistics implementation is introduced.
 Boundary: This bridge establishes deterministic weighted finite-list covariance for composite test scores. Gaussian conditional distributions, independent sampling and all confidence-coverage claims remain unproved.
*)

Definition four_batch_score {A:Type} (x1 x2 x3 x4:A->R) (a1 a2 a3 a4:R) : A->R :=
 fun t => (a1*x1 t+a2*x2 t)+(a3*x3 t+a4*x4 t).

(** [four_batch_covariance_bilinear] (theorem).
 Mathematical meaning: The sample covariance between two four-score composites equals the 4-by-4 symbolic bilinear form evaluated at the ten actual weighted sample variances and covariances.
 Exact checked proposition: forall A w x1 x2 x3 x4 xs a1..b4, mass <> 0 -> covariance(score(a),score(b)) = four_covariant(sample_covariance_matrix,a,b).
 Premises and side conditions: The four input observations and arbitrary finite batch identifiers are exact real-valued functions. Total sample exposure must be nonzero for a quotient-level covariance identity. Symbolic covariance entries are instantiated by actual sample moment definitions, not unconstrained arbitrary matrix symbols.
 Proof/definition method: Expand each composite into two score pairs using the seven already checked finite-sample covariance bridge theorems, use symmetry and covariance-self variance, and normalize the remaining polynomial with ring.
 Library reuse: The canonical FiniteSum and ListPoolingAlgebra covariance, variance and linearity theorems are reused directly; Rocq Stdlib Ring/Field handles only real algebra and no new statistics implementation is introduced.
 Boundary: This bridge establishes deterministic weighted finite-list covariance for composite test scores. Gaussian conditional distributions, independent sampling and all confidence-coverage claims remain unproved.
*)

Theorem four_batch_covariance_bilinear :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A)
        (a1 a2 a3 a4 b1 b2 b3 b4:R),
  batch_mass w xs<>0 ->
  batch_covariance w
   (four_batch_score x1 x2 x3 x4 a1 a2 a3 a4)
   (four_batch_score x1 x2 x3 x4 b1 b2 b3 b4) xs =
  four_covariant
   (batch_variance w x1 xs) (batch_variance w x2 xs)
   (batch_variance w x3 xs) (batch_variance w x4 xs)
   (batch_covariance w x1 x2 xs) (batch_covariance w x1 x3 xs)
   (batch_covariance w x1 x4 xs) (batch_covariance w x2 x3 xs)
   (batch_covariance w x2 x4 xs) (batch_covariance w x3 x4 xs)
   a1 a2 a3 a4 b1 b2 b3 b4.
Proof.
 intros A w x1 x2 x3 x4 xs a1 a2 a3 a4 b1 b2 b3 b4 Hm.
 unfold four_batch_score.
 rewrite four_batch_covariance_add_left by exact Hm.
 rewrite !four_batch_covariance_add_right by exact Hm.
 rewrite !four_batch_covariance_linear_left by exact Hm.
 rewrite !batch_covariance_scale_right by exact Hm.
 rewrite !batch_covariance_self_variance.
 rewrite (batch_covariance_symmetry A w x2 x1 xs).
 rewrite (batch_covariance_symmetry A w x3 x1 xs).
 rewrite (batch_covariance_symmetry A w x4 x1 xs).
 rewrite (batch_covariance_symmetry A w x3 x2 xs).
 rewrite (batch_covariance_symmetry A w x4 x2 xs).
 rewrite (batch_covariance_symmetry A w x4 x3 xs).
 cbv [four_covariant].
 ring.
Qed.

(** [four_batch_variance_quadratic] (theorem).
 Mathematical meaning: The finite-sample variance of a four-test composite is exactly the symbolic covariance quadratic evaluated on the ten observed covariance-matrix entries.
 Exact checked proposition: forall A w x1 x2 x3 x4 xs a1..a4, mass <> 0 -> variance(score(a)) = quadratic(actual_sample_covariances,a).
 Premises and side conditions: The four input observations and arbitrary finite batch identifiers are exact real-valued functions. Total sample exposure must be nonzero for a quotient-level covariance identity. Symbolic covariance entries are instantiated by actual sample moment definitions, not unconstrained arbitrary matrix symbols.
 Proof/definition method: Apply the general kernel-checked composite covariance bridge to a coefficient vector paired with itself, then use the existing covariance-self variance theorem.
 Library reuse: The canonical FiniteSum and ListPoolingAlgebra covariance, variance and linearity theorems are reused directly; Rocq Stdlib Ring/Field handles only real algebra and no new statistics implementation is introduced.
 Boundary: This bridge establishes deterministic weighted finite-list covariance for composite test scores. Gaussian conditional distributions, independent sampling and all confidence-coverage claims remain unproved.
*)

Theorem four_batch_variance_quadratic :
 forall (A:Type) (w x1 x2 x3 x4:A->R) (xs:list A)
        (a1 a2 a3 a4:R),
  batch_mass w xs<>0 ->
  batch_variance w (four_batch_score x1 x2 x3 x4 a1 a2 a3 a4) xs =
  four_quadratic
   (batch_variance w x1 xs) (batch_variance w x2 xs)
   (batch_variance w x3 xs) (batch_variance w x4 xs)
   (batch_covariance w x1 x2 xs) (batch_covariance w x1 x3 xs)
   (batch_covariance w x1 x4 xs) (batch_covariance w x2 x3 xs)
   (batch_covariance w x2 x4 xs) (batch_covariance w x3 x4 xs)
   a1 a2 a3 a4.
Proof.
 intros A w x1 x2 x3 x4 xs a1 a2 a3 a4 Hm.
 unfold four_quadratic.
 rewrite <- (batch_covariance_self_variance A w
   (four_batch_score x1 x2 x3 x4 a1 a2 a3 a4) xs).
 apply four_batch_covariance_bilinear; exact Hm.
Qed.

