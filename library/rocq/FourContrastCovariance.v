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
From Stdlib Require Import Reals Ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
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
  intros; unfold four_covariant, four_quadratic; ring.
Qed.

