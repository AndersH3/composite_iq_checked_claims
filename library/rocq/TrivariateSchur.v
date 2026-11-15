(** Module: TrivariateSchur.v
 Purpose: Establish exact determinant identities, Schur residual bounds,
 positive-semidefinite consequences and singular conditional-covariance cases
 required by the sequential-IQ and three-test-admissions covariance models.
 Mathematical representation: A real symmetric 3x3 covariance candidate
 has diagonal entries u,v,w and off-diagonals p,q,r. The two conditioned
 residual numerators are u*w-q^2 and v*w-r^2, and their cross term p*w-q*r.
 Explicit hypotheses: The factorization is unconditional real algebra;
 sign equivalences require w>0 and all other positivity, nonzero and
 singularity assumptions are stated explicitly by each theorem.
 Library use: Rocq Stdlib.Reals, Lra, Psatz and Ring; previously maintained
 finite covariance/Schur algebra is conceptually reused, not reimplemented
 using a custom matrix, probability mass, integration or summation library.
 Limitations: These exact polynomial statements neither construct a
 multivariate Gaussian distribution nor prove Gaussian conditional laws,
 normal-tail integrals, characteristic functions or empirical IQ parameters.
 Reproduction: scripts/compile_rocq.sh using the pinned Rocq 9.2 compiler
 in the project CI workflow, after the canonical covariance modules.
 AI disclosure: AI-assisted statement design, proofs and documentation;
 only a successful pinned kernel build validates the exact propositions.
*)
From Stdlib Require Import Reals Lra Psatz Ring.
Open Scope R_scope.

(**
 [tri_left] (definition) — The first unnormalized conditional residual variance, for conditioning variance w.
 Mathematical meaning: The first unnormalized conditional residual variance, for conditioning variance w. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact declaration: Definition tri_left (u w q : R) : R := u*w-q*q
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: A transparent real polynomial without independent probability or matrix implementations.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Definition tri_left (u w q : R) : R := u*w-q*q.

(**
 [tri_right] (definition) — The second unnormalized conditional residual variance, for conditioning variance w.
 Mathematical meaning: The second unnormalized conditional residual variance, for conditioning variance w. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact declaration: Definition tri_right (v w r : R) : R := v*w-r*r
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: A transparent real polynomial without independent probability or matrix implementations.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Definition tri_right (v w r : R) : R := v*w-r*r.

(**
 [tri_cross] (definition) — The unnormalized conditional covariance between the first two variables.
 Mathematical meaning: The unnormalized conditional covariance between the first two variables. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact declaration: Definition tri_cross (p w q r : R) : R := p*w-q*r
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: A transparent real polynomial without independent probability or matrix implementations.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Definition tri_cross (p w q r : R) : R := p*w-q*r.

(**
 [tri_determinant] (definition) — The determinant of the symmetric trivariate covariance candidate.
 Mathematical meaning: The determinant of the symmetric trivariate covariance candidate. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact declaration: Definition tri_determinant (u v w p q r : R) : R := u*v*w + 2*p*q*r - u*r*r - v*q*q - w*p*p
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: A transparent real polynomial without independent probability or matrix implementations.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Definition tri_determinant (u v w p q r : R) : R := u*v*w + 2*p*q*r - u*r*r - v*q*q - w*p*p.

(**
 [trivariate_factor] (theorem) — The exact three-variable Schur determinant factorization.
 Mathematical meaning: The exact three-variable Schur determinant factorization. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, ((tri_left u w q) * (tri_right v w r)) - ((tri_cross p w q r) * (tri_cross p w q r)) = w * (tri_determinant u v w p q r).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_factor :
  forall u v w p q r : R, ((tri_left u w q) * (tri_right v w r)) - ((tri_cross p w q r) * (tri_cross p w q r)) = w * (tri_determinant u v w p q r).
Proof.
  intros u v w p q r.
  unfold tri_left, tri_right, tri_cross, tri_determinant; ring.
Qed.

(**
 [trivariate_balance] (theorem) — The residual product is the sum of squared conditional cross-covariance and the determinant contribution.
 Mathematical meaning: The residual product is the sum of squared conditional cross-covariance and the determinant contribution. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, ((tri_left u w q) * (tri_right v w r)) = ((tri_cross p w q r) * (tri_cross p w q r)) + w * (tri_determinant u v w p q r).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_balance :
  forall u v w p q r : R, ((tri_left u w q) * (tri_right v w r)) = ((tri_cross p w q r) * (tri_cross p w q r)) + w * (tri_determinant u v w p q r).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_singular_implies_tight] (theorem) — A zero trivariate determinant gives exact saturation of the residual covariance inequality.
 Mathematical meaning: A zero trivariate determinant gives exact saturation of the residual covariance inequality. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, (tri_determinant u v w p q r) = 0 -> ((tri_left u w q) * (tri_right v w r)) = ((tri_cross p w q r) * (tri_cross p w q r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_singular_implies_tight :
  forall u v w p q r : R, (tri_determinant u v w p q r) = 0 -> ((tri_left u w q) * (tri_right v w r)) = ((tri_cross p w q r) * (tri_cross p w q r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_tight_iff_singular] (theorem) — For positive conditioning variance, tightness is equivalent to a zero determinant.
 Mathematical meaning: For positive conditioning variance, tightness is equivalent to a zero determinant. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (((tri_left u w q) * (tri_right v w r)) = ((tri_cross p w q r) * (tri_cross p w q r)) <-> (tri_determinant u v w p q r) = 0).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_tight_iff_singular :
  forall u v w p q r : R, 0 < w -> (((tri_left u w q) * (tri_right v w r)) = ((tri_cross p w q r) * (tri_cross p w q r)) <-> (tri_determinant u v w p q r) = 0).
Proof.
  intros u v w p q r Hw.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  split; intro Hsign; nra.
Qed.

(**
 [trivariate_positive_iff_strict] (theorem) — Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap.
 Mathematical meaning: Positive determinant is equivalent to a strict Schur Cauchy-Schwarz gap. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (0 < (tri_determinant u v w p q r) <-> ((tri_cross p w q r) * (tri_cross p w q r)) < ((tri_left u w q) * (tri_right v w r))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_positive_iff_strict :
  forall u v w p q r : R, 0 < w -> (0 < (tri_determinant u v w p q r) <-> ((tri_cross p w q r) * (tri_cross p w q r)) < ((tri_left u w q) * (tri_right v w r))).
Proof.
  intros u v w p q r Hw.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  split; intro Hsign; nra.
Qed.

(**
 [trivariate_negative_iff_reverse] (theorem) — Negative determinant is equivalent to strict reversal of the Schur inequality.
 Mathematical meaning: Negative determinant is equivalent to strict reversal of the Schur inequality. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> ((tri_determinant u v w p q r) < 0 <-> ((tri_left u w q) * (tri_right v w r)) < ((tri_cross p w q r) * (tri_cross p w q r))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_negative_iff_reverse :
  forall u v w p q r : R, 0 < w -> ((tri_determinant u v w p q r) < 0 <-> ((tri_left u w q) * (tri_right v w r)) < ((tri_cross p w q r) * (tri_cross p w q r))).
Proof.
  intros u v w p q r Hw.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  split; intro Hsign; nra.
Qed.

(**
 [trivariate_nonnegative_iff_weak] (theorem) — Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality.
 Mathematical meaning: Nonnegative determinant is equivalent to the weak Schur Cauchy-Schwarz inequality. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (0 <= (tri_determinant u v w p q r) <-> ((tri_cross p w q r) * (tri_cross p w q r)) <= ((tri_left u w q) * (tri_right v w r))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_nonnegative_iff_weak :
  forall u v w p q r : R, 0 < w -> (0 <= (tri_determinant u v w p q r) <-> ((tri_cross p w q r) * (tri_cross p w q r)) <= ((tri_left u w q) * (tri_right v w r))).
Proof.
  intros u v w p q r Hw.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  split; intro Hsign; nra.
Qed.

(**
 [trivariate_nonpositive_iff_reverse_weak] (theorem) — Nonpositive determinant is equivalent to the reverse weak residual inequality.
 Mathematical meaning: Nonpositive determinant is equivalent to the reverse weak residual inequality. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> ((tri_determinant u v w p q r) <= 0 <-> ((tri_left u w q) * (tri_right v w r)) <= ((tri_cross p w q r) * (tri_cross p w q r))).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_nonpositive_iff_reverse_weak :
  forall u v w p q r : R, 0 < w -> ((tri_determinant u v w p q r) <= 0 <-> ((tri_left u w q) * (tri_right v w r)) <= ((tri_cross p w q r) * (tri_cross p w q r))).
Proof.
  intros u v w p q r Hw.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  split; intro Hsign; nra.
Qed.

(**
 [trivariate_strict_positive_bound] (theorem) — A positive determinant forces a strict conditional Cauchy-Schwarz bound.
 Mathematical meaning: A positive determinant forces a strict conditional Cauchy-Schwarz bound. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> ((tri_cross p w q r) * (tri_cross p w q r)) < ((tri_left u w q) * (tri_right v w r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_strict_positive_bound :
  forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> ((tri_cross p w q r) * (tri_cross p w q r)) < ((tri_left u w q) * (tri_right v w r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_strict_negative_bound] (theorem) — A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound.
 Mathematical meaning: A negative determinant forces a strict reverse conditional Cauchy-Schwarz bound. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (tri_determinant u v w p q r) < 0 -> ((tri_left u w q) * (tri_right v w r)) < ((tri_cross p w q r) * (tri_cross p w q r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_strict_negative_bound :
  forall u v w p q r : R, 0 < w -> (tri_determinant u v w p q r) < 0 -> ((tri_left u w q) * (tri_right v w r)) < ((tri_cross p w q r) * (tri_cross p w q r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_weak_positive_bound] (theorem) — A nonnegative determinant bounds squared conditional covariance by the residual product.
 Mathematical meaning: A nonnegative determinant bounds squared conditional covariance by the residual product. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> ((tri_cross p w q r) * (tri_cross p w q r)) <= ((tri_left u w q) * (tri_right v w r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_weak_positive_bound :
  forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> ((tri_cross p w q r) * (tri_cross p w q r)) <= ((tri_left u w q) * (tri_right v w r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_weak_negative_bound] (theorem) — A nonpositive determinant bounds the residual product by squared conditional covariance.
 Mathematical meaning: A nonpositive determinant bounds the residual product by squared conditional covariance. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (tri_determinant u v w p q r) <= 0 -> ((tri_left u w q) * (tri_right v w r)) <= ((tri_cross p w q r) * (tri_cross p w q r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_weak_negative_bound :
  forall u v w p q r : R, 0 < w -> (tri_determinant u v w p q r) <= 0 -> ((tri_left u w q) * (tri_right v w r)) <= ((tri_cross p w q r) * (tri_cross p w q r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_cross_factor] (theorem) — Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant.
 Mathematical meaning: Conditional uncorrelatedness makes the residual product exactly the conditioning variance times the determinant. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, (tri_cross p w q r) = 0 -> ((tri_left u w q) * (tri_right v w r)) = w * (tri_determinant u v w p q r).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_cross_factor :
  forall u v w p q r : R, (tri_cross p w q r) = 0 -> ((tri_left u w q) * (tri_right v w r)) = w * (tri_determinant u v w p q r).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_cross_positive_product] (theorem) — Conditional uncorrelatedness and positive determinant imply a strictly positive residual product.
 Mathematical meaning: Conditional uncorrelatedness and positive determinant imply a strictly positive residual product. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (tri_cross p w q r) = 0 -> 0 < (tri_determinant u v w p q r) -> 0 < ((tri_left u w q) * (tri_right v w r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_cross_positive_product :
  forall u v w p q r : R, 0 < w -> (tri_cross p w q r) = 0 -> 0 < (tri_determinant u v w p q r) -> 0 < ((tri_left u w q) * (tri_right v w r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_cross_singular_product] (theorem) — Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish.
 Mathematical meaning: Conditional uncorrelatedness with singular determinant forces at least one residual factor to vanish. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, (tri_cross p w q r) = 0 -> (tri_determinant u v w p q r) = 0 -> ((tri_left u w q) * (tri_right v w r)) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_cross_singular_product :
  forall u v w p q r : R, (tri_cross p w q r) = 0 -> (tri_determinant u v w p q r) = 0 -> ((tri_left u w q) * (tri_right v w r)) = 0.
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_left_determinant] (theorem) — Vanishing first residual gives an exact negative-square identity.
 Mathematical meaning: Vanishing first residual gives an exact negative-square identity. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, (tri_left u w q) = 0 -> w * (tri_determinant u v w p q r) = - ((tri_cross p w q r) * (tri_cross p w q r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_left_determinant :
  forall u v w p q r : R, (tri_left u w q) = 0 -> w * (tri_determinant u v w p q r) = - ((tri_cross p w q r) * (tri_cross p w q r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_right_determinant] (theorem) — Vanishing second residual gives an exact negative-square identity.
 Mathematical meaning: Vanishing second residual gives an exact negative-square identity. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, (tri_right v w r) = 0 -> w * (tri_determinant u v w p q r) = - ((tri_cross p w q r) * (tri_cross p w q r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_right_determinant :
  forall u v w p q r : R, (tri_right v w r) = 0 -> w * (tri_determinant u v w p q r) = - ((tri_cross p w q r) * (tri_cross p w q r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_left_cross_nonzero_negative] (theorem) — A zero first residual with nonzero conditional cross-covariance forces negative determinant.
 Mathematical meaning: A zero first residual with nonzero conditional cross-covariance forces negative determinant. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (tri_left u w q) = 0 -> (tri_cross p w q r) <> 0 -> (tri_determinant u v w p q r) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_left_cross_nonzero_negative :
  forall u v w p q r : R, 0 < w -> (tri_left u w q) = 0 -> (tri_cross p w q r) <> 0 -> (tri_determinant u v w p q r) < 0.
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_right_cross_nonzero_negative] (theorem) — A zero second residual with nonzero conditional cross-covariance forces negative determinant.
 Mathematical meaning: A zero second residual with nonzero conditional cross-covariance forces negative determinant. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> (tri_right v w r) = 0 -> (tri_cross p w q r) <> 0 -> (tri_determinant u v w p q r) < 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_right_cross_nonzero_negative :
  forall u v w p q r : R, 0 < w -> (tri_right v w r) = 0 -> (tri_cross p w q r) <> 0 -> (tri_determinant u v w p q r) < 0.
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_left_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness.
 Mathematical meaning: Under a nonnegative determinant, zero first residual forces conditional uncorrelatedness. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> (tri_left u w q) = 0 -> (tri_cross p w q r) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_left_psd_forces_zero_cross :
  forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> (tri_left u w q) = 0 -> (tri_cross p w q r) = 0.
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_zero_right_psd_forces_zero_cross] (theorem) — Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness.
 Mathematical meaning: Under a nonnegative determinant, zero second residual forces conditional uncorrelatedness. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> (tri_right v w r) = 0 -> (tri_cross p w q r) = 0.
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_zero_right_psd_forces_zero_cross :
  forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> (tri_right v w r) = 0 -> (tri_cross p w q r) = 0.
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_positive_det_left_forces_right] (theorem) — Positive determinant and positive first residual force a positive second residual.
 Mathematical meaning: Positive determinant and positive first residual force a positive second residual. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> 0 < (tri_left u w q) -> 0 < (tri_right v w r).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_positive_det_left_forces_right :
  forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> 0 < (tri_left u w q) -> 0 < (tri_right v w r).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_positive_det_right_forces_left] (theorem) — Positive determinant and positive second residual force a positive first residual.
 Mathematical meaning: Positive determinant and positive second residual force a positive first residual. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> 0 < (tri_right v w r) -> 0 < (tri_left u w q).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_positive_det_right_forces_left :
  forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> 0 < (tri_right v w r) -> 0 < (tri_left u w q).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_nonnegative_det_left_forces_right] (theorem) — A nonnegative determinant and strict first residual positivity force nonnegative second residual.
 Mathematical meaning: A nonnegative determinant and strict first residual positivity force nonnegative second residual. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> 0 < (tri_left u w q) -> 0 <= (tri_right v w r).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_nonnegative_det_left_forces_right :
  forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> 0 < (tri_left u w q) -> 0 <= (tri_right v w r).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_nonnegative_det_right_forces_left] (theorem) — A nonnegative determinant and strict second residual positivity force nonnegative first residual.
 Mathematical meaning: A nonnegative determinant and strict second residual positivity force nonnegative first residual. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> 0 < (tri_right v w r) -> 0 <= (tri_left u w q).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_nonnegative_det_right_forces_left :
  forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> 0 < (tri_right v w r) -> 0 <= (tri_left u w q).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_positive_det_positive_product] (theorem) — A strictly positive determinant forces both Schur residual factors to have a positive product.
 Mathematical meaning: A strictly positive determinant forces both Schur residual factors to have a positive product. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> 0 < ((tri_left u w q) * (tri_right v w r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_positive_det_positive_product :
  forall u v w p q r : R, 0 < w -> 0 < (tri_determinant u v w p q r) -> 0 < ((tri_left u w q) * (tri_right v w r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

(**
 [trivariate_nonnegative_det_nonnegative_product] (theorem) — A nonnegative determinant forces the Schur residual product to be nonnegative.
 Mathematical meaning: A nonnegative determinant forces the Schur residual product to be nonnegative. The result is used to audit conditional covariance or precision in a three-test score model.
 Exact checked proposition: forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> 0 <= ((tri_left u w q) * (tri_right v w r)).
 Premises and side conditions: All scalar quantities are real. Strict conditioning variance and any determinant, residual or nonzero assumptions are explicit in the statement; no positive semidefinite matrix is silently assumed.
 Proof/definition method: Deduction from the exact trivariate Schur factorization using canonical real polynomial normalization, inequalities and elementary real algebra.
 Library reuse: Rocq standard Reals, Lra, Psatz and Ring, rather than a custom algebra solver or a duplicate probability-sum implementation.
 Boundary: Exact 3x3 covariance-candidate algebra; no continuous Gaussian conditional law, normal tail or empirical psychometric assertion is proved here.
*)
Theorem trivariate_nonnegative_det_nonnegative_product :
  forall u v w p q r : R, 0 < w -> 0 <= (tri_determinant u v w p q r) -> 0 <= ((tri_left u w q) * (tri_right v w r)).
Proof.
  intros u v w p q r.
  pose proof (trivariate_factor u v w p q r) as Hfactor.
  nra.
Qed.

