(** Module: TwoObservationSchur.v
 Purpose: Verify the covariance-block inverse, two-observation linear
 least-squares regression, Schur residual variance and exact information
 gain needed by the Gaussian-regression algebra in the three reports.
 Mathematical representation: A symmetric 2-by-2 real covariance block
 with diagonal entries a,b, cross covariance c and target cross covariances
 u,v. A target variance s yields an exact finite covariance regression
 quadratic polynomial. Neither a Gaussian distribution nor new matrix
 infrastructure is assumed.
 Explicit hypotheses: Nonzero determinant for inverse identities, positive
 leading variance and determinant for strict optimality and information
 inequalities, and full 3-by-3 quadratic positivity where Schur
 nonnegativity is asserted. Degenerate boundaries are not divided by.
 Library use: Rocq Stdlib.Reals, Lra, Psatz, Field and Ring tactics; existing
 finite covariance and equicorrelation regression work informs the model.
 All covariance block calculations use standard real ring/field arithmetic,
 not a custom recursive matrix or finite-list implementation.
 Limitations: These are deterministic two-observation covariance and
 linear least-squares results, NOT a proof of Gaussian conditioning,
 bivariate normal tail integrals, normal CDF/quantiles, or IQ population
 assumptions. For conditional distribution claims see REPORT_THEOREM_INVENTORY.
 Reproduction: After the existing Rocq modules, run
 rocq compile TwoObservationSchur.v in pinned Rocq Prover 9.2 CI.
 AI disclosure: OpenAI authored these source statements and proofs.
 Correctness is determined by the Rocq kernel's independent check.
 *)
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

(**
 [cov2_det] (definition) — The determinant of the general symmetric 2-by-2 covariance block.
 Mathematical meaning: The determinant of the general symmetric 2-by-2 covariance block.
 Exact declaration: Definition cov2_det (a b c : R) : R := a*b-c*c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_det (a b c : R) : R := a*b-c*c.

(**
 [cov2_quad] (definition) — The quadratic form of a general symmetric two-observation covariance block.
 Mathematical meaning: The quadratic form of a general symmetric two-observation covariance block.
 Exact declaration: Definition cov2_quad (a b c x y : R) : R := a*x*x+2*c*x*y+b*y*y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_quad (a b c x y : R) : R :=
 a*x*x+2*c*x*y+b*y*y.

(**
 [cov2_beta_first] (definition) — The first coordinate of the general two-observation linear regression coefficient C B^{-1}.
 Mathematical meaning: The first coordinate of the general two-observation linear regression coefficient C B^{-1}.
 Exact declaration: Definition cov2_beta_first (a b c u v : R) : R := (b*u-c*v)/cov2_det a b c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_beta_first (a b c u v : R) : R :=
 (b*u-c*v)/cov2_det a b c.

(**
 [cov2_beta_second] (definition) — The second coordinate of the general two-observation linear regression coefficient C B^{-1}.
 Mathematical meaning: The second coordinate of the general two-observation linear regression coefficient C B^{-1}.
 Exact declaration: Definition cov2_beta_second (a b c u v : R) : R := (a*v-c*u)/cov2_det a b c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_beta_second (a b c u v : R) : R :=
 (a*v-c*u)/cov2_det a b c.

(**
 [cov2_risk] (definition) — The exact quadratic least-squares risk polynomial for predicting one target from two observations.
 Mathematical meaning: The exact quadratic least-squares risk polynomial for predicting one target from two observations.
 Exact declaration: Definition cov2_risk (a b c u v s x y : R) : R := s-2*u*x-2*v*y+cov2_quad a b c x y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_risk (a b c u v s x y : R) : R :=
 s-2*u*x-2*v*y+cov2_quad a b c x y.

(**
 [cov2_schur] (definition) — The conditional-residual Schur complement variance expressed using the two optimal regression coefficients.
 Mathematical meaning: The conditional-residual Schur complement variance expressed using the two optimal regression coefficients.
 Exact declaration: Definition cov2_schur (a b c u v s : R) : R := s-u*cov2_beta_first a b c u v-v*cov2_beta_second a b c u v.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_schur (a b c u v s : R) : R :=
 s-u*cov2_beta_first a b c u v-v*cov2_beta_second a b c u v.

(**
 [cov2_one_risk] (definition) — The optimal variance from predicting with the first observed coordinate alone.
 Mathematical meaning: The optimal variance from predicting with the first observed coordinate alone.
 Exact declaration: Definition cov2_one_risk (a u s : R) : R := s-u*u/a.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_one_risk (a u s : R) : R := s-u*u/a.

(**
 [cov2_predict] (definition) — The affine optimal two-observation predictor at observed scores and specified mean values.
 Mathematical meaning: The affine optimal two-observation predictor at observed scores and specified mean values.
 Exact declaration: Definition cov2_predict (mu mu1 mu2 a b c u v x y : R) : R := mu + cov2_beta_first a b c u v*(x-mu1) + cov2_beta_second a b c u v*(y-mu2).
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: A transparent scalar covariance or prediction expression using Rocq's standard field operators.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Definition cov2_predict (mu mu1 mu2 a b c u v x y : R) : R :=
 mu + cov2_beta_first a b c u v*(x-mu1)
    + cov2_beta_second a b c u v*(y-mu2).

(**
 [cov2_det_symmetric] (theorem) — Swapping the two observed variables preserves the covariance determinant.
 Mathematical meaning: Swapping the two observed variables preserves the covariance determinant.
 Exact checked proposition: forall a b c, cov2_det a b c = cov2_det b a c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_det_symmetric :
 forall a b c, cov2_det a b c = cov2_det b a c.
Proof.
 intros; unfold cov2_det; ring.
Qed.

(**
 [cov2_det_psd_bound] (theorem) — The bivariate Cauchy covariance bound implies a nonnegative block determinant.
 Mathematical meaning: The bivariate Cauchy covariance bound implies a nonnegative block determinant.
 Exact checked proposition: forall a b c, c*c<=a*b -> 0<=cov2_det a b c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_det_psd_bound :
 forall a b c, c*c<=a*b -> 0<=cov2_det a b c.
Proof.
 intros a b c H; unfold cov2_det; lra.
Qed.

(**
 [cov2_det_pd_bound] (theorem) — The strict bivariate covariance bound implies an invertible positive determinant.
 Mathematical meaning: The strict bivariate covariance bound implies an invertible positive determinant.
 Exact checked proposition: forall a b c, c*c<a*b -> 0<cov2_det a b c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_det_pd_bound :
 forall a b c, c*c<a*b -> 0<cov2_det a b c.
Proof.
 intros a b c H; unfold cov2_det; lra.
Qed.

(**
 [cov2_beta_first_normal_equation] (theorem) — The first inverse-covariance coefficient satisfies the first full two-observation regression normal equation.
 Mathematical meaning: The first inverse-covariance coefficient satisfies the first full two-observation regression normal equation.
 Exact checked proposition: forall a b c u v, cov2_det a b c<>0 -> a*cov2_beta_first a b c u v+c*cov2_beta_second a b c u v=u.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_first_normal_equation :
 forall a b c u v,
 cov2_det a b c<>0 ->
 a*cov2_beta_first a b c u v+c*cov2_beta_second a b c u v=u.
Proof.
 intros a b c u v Hd.
 unfold cov2_beta_first,cov2_beta_second,cov2_det in *.
 field; exact Hd.
Qed.

(**
 [cov2_beta_second_normal_equation] (theorem) — The second inverse-covariance coefficient satisfies the second full regression normal equation.
 Mathematical meaning: The second inverse-covariance coefficient satisfies the second full regression normal equation.
 Exact checked proposition: forall a b c u v, cov2_det a b c<>0 -> c*cov2_beta_first a b c u v+b*cov2_beta_second a b c u v=v.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_second_normal_equation :
 forall a b c u v,
 cov2_det a b c<>0 ->
 c*cov2_beta_first a b c u v+b*cov2_beta_second a b c u v=v.
Proof.
 intros a b c u v Hd.
 unfold cov2_beta_first,cov2_beta_second,cov2_det in *.
 field; exact Hd.
Qed.

(**
 [cov2_normal_equations_unique] (theorem) — The invertible symmetric two-observation covariance block has a unique simultaneous linear regression solution.
 Mathematical meaning: The invertible symmetric two-observation covariance block has a unique simultaneous linear regression solution.
 Exact checked proposition: forall a b c u v x y, cov2_det a b c<>0 -> a*x+c*y=u -> c*x+b*y=v -> x=cov2_beta_first a b c u v /\ y=cov2_beta_second a b c u v.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_normal_equations_unique :
 forall a b c u v x y,
 cov2_det a b c<>0 ->
 a*x+c*y=u -> c*x+b*y=v ->
 x=cov2_beta_first a b c u v /\
 y=cov2_beta_second a b c u v.
Proof.
 intros a b c u v x y Hd H1 H2.
 assert (Hr1:b*(a*x+c*y)-c*(c*x+b*y)=b*u-c*v)
   by (rewrite H1,H2; ring).
 assert (Hr2:a*(c*x+b*y)-c*(a*x+c*y)=a*v-c*u)
   by (rewrite H2,H1; ring).
 assert (He1:cov2_det a b c*x=b*u-c*v)
   by (unfold cov2_det; nra).
 assert (He2:cov2_det a b c*y=a*v-c*u)
   by (unfold cov2_det; nra).
 split.
 - unfold cov2_beta_first; rewrite <- He1; field; exact Hd.
 - unfold cov2_beta_second; rewrite <- He2; field; exact Hd.
Qed.

(**
 [cov2_beta_swap_first] (theorem) — Swapping the observed covariance coordinates exchanges the first and second regression coefficients.
 Mathematical meaning: Swapping the observed covariance coordinates exchanges the first and second regression coefficients.
 Exact checked proposition: forall a b c u v, cov2_beta_first a b c u v = cov2_beta_second b a c v u.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_swap_first :
 forall a b c u v,
 cov2_beta_first a b c u v = cov2_beta_second b a c v u.
Proof.
 intros; unfold cov2_beta_first,cov2_beta_second,cov2_det.
 f_equal; ring.
Qed.

(**
 [cov2_beta_swap_second] (theorem) — Swapping the observed covariance coordinates exchanges the second and first regression coefficients.
 Mathematical meaning: Swapping the observed covariance coordinates exchanges the second and first regression coefficients.
 Exact checked proposition: forall a b c u v, cov2_beta_second a b c u v = cov2_beta_first b a c v u.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_swap_second :
 forall a b c u v,
 cov2_beta_second a b c u v = cov2_beta_first b a c v u.
Proof.
 intros; unfold cov2_beta_first,cov2_beta_second,cov2_det.
 f_equal; ring.
Qed.

(**
 [cov2_beta_first_linear] (theorem) — The first multivariate regression coefficient is additive in the target-observation cross-covariance vector.
 Mathematical meaning: The first multivariate regression coefficient is additive in the target-observation cross-covariance vector.
 Exact checked proposition: forall a b c u v u' v', cov2_beta_first a b c (u+u') (v+v') = cov2_beta_first a b c u v + cov2_beta_first a b c u' v'.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_first_linear :
 forall a b c u v u' v',
 cov2_beta_first a b c (u+u') (v+v') =
 cov2_beta_first a b c u v + cov2_beta_first a b c u' v'.
Proof.
 intros; unfold cov2_beta_first.
 unfold Rdiv.
 ring.
Qed.

(**
 [cov2_beta_second_linear] (theorem) — The second multivariate regression coefficient is additive in the target-observation cross-covariance vector.
 Mathematical meaning: The second multivariate regression coefficient is additive in the target-observation cross-covariance vector.
 Exact checked proposition: forall a b c u v u' v', cov2_beta_second a b c (u+u') (v+v') = cov2_beta_second a b c u v + cov2_beta_second a b c u' v'.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_second_linear :
 forall a b c u v u' v',
 cov2_beta_second a b c (u+u') (v+v') =
 cov2_beta_second a b c u v + cov2_beta_second a b c u' v'.
Proof.
 intros; unfold cov2_beta_second.
 unfold Rdiv.
 ring.
Qed.

(**
 [cov2_beta_first_homogeneous] (theorem) — The first multivariate regression coefficient scales exactly with the target score scale.
 Mathematical meaning: The first multivariate regression coefficient scales exactly with the target score scale.
 Exact checked proposition: forall a b c u v k, cov2_beta_first a b c (k*u) (k*v) = k*cov2_beta_first a b c u v.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_first_homogeneous :
 forall a b c u v k,
 cov2_beta_first a b c (k*u) (k*v) =
 k*cov2_beta_first a b c u v.
Proof.
 intros; unfold cov2_beta_first,Rdiv; ring.
Qed.

(**
 [cov2_beta_second_homogeneous] (theorem) — The second multivariate regression coefficient scales exactly with the target score scale.
 Mathematical meaning: The second multivariate regression coefficient scales exactly with the target score scale.
 Exact checked proposition: forall a b c u v k, cov2_beta_second a b c (k*u) (k*v) = k*cov2_beta_second a b c u v.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_second_homogeneous :
 forall a b c u v k,
 cov2_beta_second a b c (k*u) (k*v) =
 k*cov2_beta_second a b c u v.
Proof.
 intros; unfold cov2_beta_second,Rdiv; ring.
Qed.

(**
 [cov2_quad_completed_square] (theorem) — The general two-dimensional covariance quadratic form is a sum of two explicitly weighted squares.
 Mathematical meaning: The general two-dimensional covariance quadratic form is a sum of two explicitly weighted squares.
 Exact checked proposition: forall a b c x y, a<>0 -> cov2_quad a b c x y = ((a*x+c*y)*(a*x+c*y))/a+(cov2_det a b c/a)*y*y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_quad_completed_square :
 forall a b c x y,
 a<>0 ->
 cov2_quad a b c x y =
 ((a*x+c*y)*(a*x+c*y))/a+(cov2_det a b c/a)*y*y.
Proof.
 intros a b c x y Ha.
 unfold cov2_quad,cov2_det.
 field; exact Ha.
Qed.

(**
 [cov2_quad_positive_semidefinite] (theorem) — Strict positivity of the leading principal variance and determinant implies the full covariance quadratic form is nonnegative.
 Mathematical meaning: Strict positivity of the leading principal variance and determinant implies the full covariance quadratic form is nonnegative.
 Exact checked proposition: forall a b c x y, 0<a -> 0<cov2_det a b c -> 0<=cov2_quad a b c x y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_quad_positive_semidefinite :
 forall a b c x y,
 0<a -> 0<cov2_det a b c ->
 0<=cov2_quad a b c x y.
Proof.
 intros a b c x y Ha Hd.
 rewrite cov2_quad_completed_square by lra.
 unfold Rdiv.
 assert (Hi:0< /a) by (apply Rinv_0_lt_compat; exact Ha).
 assert (Hsq1:0<=(a*x+c*y)*(a*x+c*y)).
 { change (0<=Rsqr (a*x+c*y)); apply Rle_0_sqr. }
 assert (Hsq2:0<=y*y).
 { change (0<=Rsqr y); apply Rle_0_sqr. }
 assert (Hfirst:0<=(a*x+c*y)*(a*x+c*y)* /a).
 { apply Rmult_le_pos; lra. }
 assert (Hsecond:0<=cov2_det a b c* /a*(y*y)).
 { apply Rmult_le_pos.
   - apply Rmult_le_pos; lra.
   - exact Hsq2. }
 lra.
Qed.

(**
 [cov2_quad_positive_definite] (theorem) — An invertible positive definite two-observation covariance block has strictly positive quadratic energy for every nonzero coefficient pair.
 Mathematical meaning: An invertible positive definite two-observation covariance block has strictly positive quadratic energy for every nonzero coefficient pair.
 Exact checked proposition: forall a b c x y, 0<a -> 0<cov2_det a b c -> (x<>0 \/ y<>0) -> 0<cov2_quad a b c x y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_quad_positive_definite :
 forall a b c x y,
 0<a -> 0<cov2_det a b c ->
 (x<>0 \/ y<>0) ->
 0<cov2_quad a b c x y.
Proof.
 intros a b c x y Ha Hd Hneq.
 rewrite cov2_quad_completed_square by lra.
 unfold Rdiv.
 assert (Hi:0< /a) by (apply Rinv_0_lt_compat; exact Ha).
 assert (Hsq:0<=(a*x+c*y)*(a*x+c*y)).
 { change (0<=Rsqr (a*x+c*y)); apply Rle_0_sqr. }
 assert (Hfirst:0<=(a*x+c*y)*(a*x+c*y)* /a).
 { apply Rmult_le_pos; lra. }
 destruct (Req_EM_T y 0) as [Hy|Hy].
 - subst y.
   assert (Hx:x<>0) by (destruct Hneq; intuition).
   set (z:=a*x+c*0).
   assert (Hz:z<>0).
   { unfold z; nra. }
   assert (Hpos:0<z*z) by nra.
   assert (Hresult:0<z*z* /a).
   { apply Rmult_lt_0_compat; assumption. }
   subst z.
   replace (cov2_det a b c * /a * 0 * 0) with 0 by ring.
   lra.
 - assert (Hsqy:0<y*y) by nra.
   assert (Hp:0<cov2_det a b c* /a).
   { apply Rmult_lt_0_compat; assumption. }
   assert (Hsecond:0<cov2_det a b c* /a*(y*y)).
   { apply Rmult_lt_0_compat; assumption. }
   lra.
Qed.

(**
 [cov2_quad_zero_iff] (theorem) — With positive definite observed covariance, the quadratic covariance energy vanishes exactly for the zero coefficient vector.
 Mathematical meaning: With positive definite observed covariance, the quadratic covariance energy vanishes exactly for the zero coefficient vector.
 Exact checked proposition: forall a b c x y, 0<a -> 0<cov2_det a b c -> (cov2_quad a b c x y=0 <-> x=0 /\ y=0).
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_quad_zero_iff :
 forall a b c x y,
 0<a -> 0<cov2_det a b c ->
 (cov2_quad a b c x y=0 <-> x=0 /\ y=0).
Proof.
 intros a b c x y Ha Hd; split.
 - intro Hq.
   destruct (Req_EM_T x 0) as [Hx|Hx];
   destruct (Req_EM_T y 0) as [Hy|Hy]; try (split; assumption).
   + exfalso; pose proof (cov2_quad_positive_definite a b c x y Ha Hd
       (or_intror Hy)) as Hp; lra.
   + exfalso; pose proof (cov2_quad_positive_definite a b c x y Ha Hd
       (or_introl Hx)) as Hp; lra.
   + exfalso; pose proof (cov2_quad_positive_definite a b c x y Ha Hd
       (or_introl Hx)) as Hp; lra.
 - intros [Hx Hy]; subst; unfold cov2_quad; ring.
Qed.

(**
 [cov2_psd_forces_cauchy] (theorem) — If every real two-dimensional covariance quadratic form is nonnegative and the first variance is positive, the determinant must be nonnegative.
 Mathematical meaning: If every real two-dimensional covariance quadratic form is nonnegative and the first variance is positive, the determinant must be nonnegative.
 Exact checked proposition: forall a b c, 0<a -> (forall x y, 0<=cov2_quad a b c x y) -> 0<=cov2_det a b c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_psd_forces_cauchy :
 forall a b c,
 0<a -> (forall x y, 0<=cov2_quad a b c x y) ->
 0<=cov2_det a b c.
Proof.
 intros a b c Ha Hq.
 pose proof (Hq c (-a)) as Hnonneg.
 replace (cov2_quad a b c c (-a))
   with (a*cov2_det a b c) in Hnonneg.
 - nra.
 - unfold cov2_quad,cov2_det; ring.
Qed.

(**
 [cov2_beta_explained_quadratic] (theorem) — At the two-variable regression solution, the predictor's explained quadratic covariance equals its target covariance pairing.
 Mathematical meaning: At the two-variable regression solution, the predictor's explained quadratic covariance equals its target covariance pairing.
 Exact checked proposition: forall a b c u v, cov2_det a b c<>0 -> cov2_quad a b c (cov2_beta_first a b c u v) (cov2_beta_second a b c u v) = u*cov2_beta_first a b c u v+v*cov2_beta_second a b c u v.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_beta_explained_quadratic :
 forall a b c u v,
 cov2_det a b c<>0 ->
 cov2_quad a b c
   (cov2_beta_first a b c u v)
   (cov2_beta_second a b c u v) =
 u*cov2_beta_first a b c u v+v*cov2_beta_second a b c u v.
Proof.
 intros a b c u v Hd.
 set (p := cov2_beta_first a b c u v).
 set (q := cov2_beta_second a b c u v).
 assert (H1:a*p+c*q=u).
 { unfold p,q; apply cov2_beta_first_normal_equation; exact Hd. }
 assert (H2:c*p+b*q=v).
 { unfold p,q; apply cov2_beta_second_normal_equation; exact Hd. }
 change (a*p*p+2*c*p*q+b*q*q=u*p+v*q).
 rewrite <- H1, <- H2.
 ring.
Qed.

(**
 [cov2_risk_completed_square] (theorem) — Every arbitrary two-observation linear prediction risk equals optimal Schur risk plus the positive covariance quadratic penalty of coefficient error.
 Mathematical meaning: Every arbitrary two-observation linear prediction risk equals optimal Schur risk plus the positive covariance quadratic penalty of coefficient error.
 Exact checked proposition: forall a b c u v s x y, cov2_det a b c<>0 -> cov2_risk a b c u v s x y = cov2_schur a b c u v s + cov2_quad a b c (x-cov2_beta_first a b c u v) (y-cov2_beta_second a b c u v).
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_risk_completed_square :
 forall a b c u v s x y,
 cov2_det a b c<>0 ->
 cov2_risk a b c u v s x y =
 cov2_schur a b c u v s +
 cov2_quad a b c
   (x-cov2_beta_first a b c u v)
   (y-cov2_beta_second a b c u v).
Proof.
 intros a b c u v s x y Hd.
 unfold cov2_risk,cov2_schur,cov2_quad,
   cov2_beta_first,cov2_beta_second,cov2_det in *.
 field; exact Hd.
Qed.

(**
 [cov2_risk_at_optimum] (theorem) — The multivariate quadratic risk evaluated at both inverse-covariance regression coefficients is exactly the Schur residual variance.
 Mathematical meaning: The multivariate quadratic risk evaluated at both inverse-covariance regression coefficients is exactly the Schur residual variance.
 Exact checked proposition: forall a b c u v s, cov2_det a b c<>0 -> cov2_risk a b c u v s (cov2_beta_first a b c u v) (cov2_beta_second a b c u v) = cov2_schur a b c u v s.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_risk_at_optimum :
 forall a b c u v s,
 cov2_det a b c<>0 ->
 cov2_risk a b c u v s
   (cov2_beta_first a b c u v)
   (cov2_beta_second a b c u v) =
 cov2_schur a b c u v s.
Proof.
 intros a b c u v s Hd.
 rewrite cov2_risk_completed_square by exact Hd.
 unfold cov2_quad; ring.
Qed.

(**
 [cov2_risk_minimizer] (theorem) — For a positive definite two-observation covariance block, the joint linear predictor globally minimizes all quadratic prediction risks.
 Mathematical meaning: For a positive definite two-observation covariance block, the joint linear predictor globally minimizes all quadratic prediction risks.
 Exact checked proposition: forall a b c u v s x y, 0<a -> 0<cov2_det a b c -> cov2_schur a b c u v s <= cov2_risk a b c u v s x y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_risk_minimizer :
 forall a b c u v s x y,
 0<a -> 0<cov2_det a b c ->
 cov2_schur a b c u v s <= cov2_risk a b c u v s x y.
Proof.
 intros a b c u v s x y Ha Hd.
 rewrite cov2_risk_completed_square by lra.
 pose proof (cov2_quad_positive_semidefinite a b c
   (x-cov2_beta_first a b c u v)
   (y-cov2_beta_second a b c u v) Ha Hd).
 lra.
Qed.

(**
 [cov2_risk_unique_minimizer] (theorem) — Strict positive definiteness makes the Schur-optimal pair of linear prediction coefficients unique.
 Mathematical meaning: Strict positive definiteness makes the Schur-optimal pair of linear prediction coefficients unique.
 Exact checked proposition: forall a b c u v s x y, 0<a -> 0<cov2_det a b c -> cov2_risk a b c u v s x y = cov2_schur a b c u v s -> x=cov2_beta_first a b c u v /\ y=cov2_beta_second a b c u v.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_risk_unique_minimizer :
 forall a b c u v s x y,
 0<a -> 0<cov2_det a b c ->
 cov2_risk a b c u v s x y = cov2_schur a b c u v s ->
 x=cov2_beta_first a b c u v /\
 y=cov2_beta_second a b c u v.
Proof.
 intros a b c u v s x y Ha Hd Hr.
 rewrite cov2_risk_completed_square in Hr by lra.
 assert (Hz : cov2_quad a b c
   (x-cov2_beta_first a b c u v)
   (y-cov2_beta_second a b c u v)=0) by lra.
 apply (proj1 (cov2_quad_zero_iff a b c _ _ Ha Hd)) in Hz.
 destruct Hz as [Hx Hy]; split; lra.
Qed.

(**
 [cov2_schur_rational] (theorem) — The two-observation conditional residual Schur complement is the exact symmetric inverse-covariance rational formula.
 Mathematical meaning: The two-observation conditional residual Schur complement is the exact symmetric inverse-covariance rational formula.
 Exact checked proposition: forall a b c u v s, cov2_det a b c<>0 -> cov2_schur a b c u v s = s-(b*u*u-2*c*u*v+a*v*v)/cov2_det a b c.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_schur_rational :
 forall a b c u v s,
 cov2_det a b c<>0 ->
 cov2_schur a b c u v s =
 s-(b*u*u-2*c*u*v+a*v*v)/cov2_det a b c.
Proof.
 intros a b c u v s Hd.
 unfold cov2_schur,cov2_beta_first,cov2_beta_second.
 field; exact Hd.
Qed.

(**
 [cov2_schur_nonnegative_from_full_psd] (theorem) — A positive-semidefinite full target-and-two-observation covariance quadratic form forces the Schur conditional residual variance to be nonnegative.
 Mathematical meaning: A positive-semidefinite full target-and-two-observation covariance quadratic form forces the Schur conditional residual variance to be nonnegative.
 Exact checked proposition: forall a b c u v s, cov2_det a b c<>0 -> (forall z x y, 0<=s*z*z-2*z*(u*x+v*y)+cov2_quad a b c x y) -> 0<=cov2_schur a b c u v s.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_schur_nonnegative_from_full_psd :
 forall a b c u v s,
 cov2_det a b c<>0 ->
 (forall z x y,
   0<=s*z*z-2*z*(u*x+v*y)+cov2_quad a b c x y) ->
 0<=cov2_schur a b c u v s.
Proof.
 intros a b c u v s Hd Hpsd.
 pose proof (Hpsd 1
   (cov2_beta_first a b c u v)
   (cov2_beta_second a b c u v)) as Hp.
 assert (Hnonneg : 0<=cov2_risk a b c u v s
   (cov2_beta_first a b c u v)
   (cov2_beta_second a b c u v)).
 { unfold cov2_risk; nra. }
 rewrite cov2_risk_at_optimum in Hnonneg by exact Hd.
 exact Hnonneg.
Qed.

(**
 [cov2_schur_le_unconditional] (theorem) — With positive observed covariance, optimal two-observation prediction cannot have greater residual variance than unconditional prediction.
 Mathematical meaning: With positive observed covariance, optimal two-observation prediction cannot have greater residual variance than unconditional prediction.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> cov2_schur a b c u v s<=s.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_schur_le_unconditional :
 forall a b c u v s,
 0<a -> 0<cov2_det a b c ->
 cov2_schur a b c u v s<=s.
Proof.
 intros a b c u v s Ha Hd.
 (* Reuse the global risk minimum at the unconditional zero predictor. *)
 pose proof (cov2_risk_minimizer a b c u v s 0 0 Ha Hd) as Hminimum.
 unfold cov2_risk, cov2_quad in Hminimum.
 nra.
Qed.

(**
 [cov2_one_to_two_gain] (theorem) — The additional explained variance supplied by a second observation is the exact squared partial covariance divided by a positive precision denominator.
 Mathematical meaning: The additional explained variance supplied by a second observation is the exact squared partial covariance divided by a positive precision denominator.
 Exact checked proposition: forall a b c u v s, a<>0 -> cov2_det a b c<>0 -> cov2_one_risk a u s-cov2_schur a b c u v s = (a*v-c*u)*(a*v-c*u)/(a*cov2_det a b c).
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_one_to_two_gain :
 forall a b c u v s,
 a<>0 -> cov2_det a b c<>0 ->
 cov2_one_risk a u s-cov2_schur a b c u v s =
 (a*v-c*u)*(a*v-c*u)/(a*cov2_det a b c).
Proof.
 intros a b c u v s Ha Hd.
 unfold cov2_one_risk,cov2_schur,cov2_beta_first,cov2_beta_second,
   cov2_det in *.
 field; nra.
Qed.

(**
 [cov2_two_obs_improves_one] (theorem) — Under strictly positive covariance principal minors, observing a second score cannot increase the best linear prediction residual variance.
 Mathematical meaning: Under strictly positive covariance principal minors, observing a second score cannot increase the best linear prediction residual variance.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> cov2_schur a b c u v s<=cov2_one_risk a u s.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_two_obs_improves_one :
 forall a b c u v s,
 0<a -> 0<cov2_det a b c ->
 cov2_schur a b c u v s<=cov2_one_risk a u s.
Proof.
 intros a b c u v s Ha Hd.
 pose proof (cov2_one_to_two_gain a b c u v s ltac:(lra) ltac:(lra)) as Hg.
 assert (Hden:0<a*cov2_det a b c) by nra.
 assert (Hi:0< /(a*cov2_det a b c))
   by (apply Rinv_0_lt_compat; exact Hden).
 assert (Hsq:0<=(a*v-c*u)*(a*v-c*u)).
 { change (0<=Rsqr (a*v-c*u)); apply Rle_0_sqr. }
 assert (Hgain:0<=(a*v-c*u)*(a*v-c*u)/(a*cov2_det a b c)).
 { unfold Rdiv; apply Rmult_le_pos; lra. }
 lra.
Qed.

(**
 [cov2_no_additional_gain_iff] (theorem) — A second observation gives no additional linear prediction improvement precisely when its partial target covariance vanishes.
 Mathematical meaning: A second observation gives no additional linear prediction improvement precisely when its partial target covariance vanishes.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> (cov2_schur a b c u v s=cov2_one_risk a u s <-> a*v=c*u).
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_no_additional_gain_iff :
 forall a b c u v s,
 0<a -> 0<cov2_det a b c ->
 (cov2_schur a b c u v s=cov2_one_risk a u s
  <-> a*v=c*u).
Proof.
 intros a b c u v s Ha Hd.
 pose proof (cov2_one_to_two_gain a b c u v s ltac:(lra) ltac:(lra)) as Hg.
 assert (Hden:0<a*cov2_det a b c) by nra.
 assert (Hi:0< /(a*cov2_det a b c))
   by (apply Rinv_0_lt_compat; exact Hden).
 unfold Rdiv in Hg.
 set (z:=a*v-c*u) in Hg.
 split; intro H.
 - assert (Hsq:z*z* /(a*cov2_det a b c)=0) by lra.
   assert (Hz:z=0).
   { apply Rmult_integral in Hsq.
     destruct Hsq as [Hzsq|Hinv0].
     - apply Rmult_integral in Hzsq.
       tauto.
     - lra. }
   unfold z in Hz; lra.
 - assert (Hz:z=0) by (unfold z; lra).
   rewrite Hz in Hg.
   lra.
Qed.

(**
 [cov2_strict_information_gain] (theorem) — If the second observation has nonzero partial target covariance, joint linear prediction improves the first-observation risk strictly.
 Mathematical meaning: If the second observation has nonzero partial target covariance, joint linear prediction improves the first-observation risk strictly.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> a*v<>c*u -> cov2_schur a b c u v s<cov2_one_risk a u s.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_strict_information_gain :
 forall a b c u v s,
 0<a -> 0<cov2_det a b c ->
 a*v<>c*u ->
 cov2_schur a b c u v s<cov2_one_risk a u s.
Proof.
 intros a b c u v s Ha Hd Hpartial.
 (* Strictness follows from weak improvement and the exact no-gain criterion. *)
 pose proof (cov2_two_obs_improves_one a b c u v s Ha Hd) as Hweak.
 assert (Hdifferent :
   cov2_schur a b c u v s <> cov2_one_risk a u s).
 { intro Heq.
   pose proof ((proj1 (cov2_no_additional_gain_iff
      a b c u v s Ha Hd)) Heq) as Hzero.
   contradiction. }
 lra.
Qed.

(**
 [cov2_schur_target_scale] (theorem) — Scaling the target score by a real factor scales its Schur residual variance by the square of that factor.
 Mathematical meaning: Scaling the target score by a real factor scales its Schur residual variance by the square of that factor.
 Exact checked proposition: forall a b c u v s k, cov2_det a b c<>0 -> cov2_schur a b c (k*u) (k*v) (k*k*s) = k*k*cov2_schur a b c u v s.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_schur_target_scale :
 forall a b c u v s k,
 cov2_det a b c<>0 ->
 cov2_schur a b c (k*u) (k*v) (k*k*s) =
 k*k*cov2_schur a b c u v s.
Proof.
 intros a b c u v s k Hd.
 unfold cov2_schur.
 rewrite cov2_beta_first_homogeneous.
 rewrite cov2_beta_second_homogeneous.
 ring.
Qed.

(**
 [cov2_predict_centered_baseline] (theorem) — At the two observation means, the affine multivariate linear predictor exactly equals the target mean.
 Mathematical meaning: At the two observation means, the affine multivariate linear predictor exactly equals the target mean.
 Exact checked proposition: forall mu mu1 mu2 a b c u v, cov2_predict mu mu1 mu2 a b c u v mu1 mu2=mu.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_predict_centered_baseline :
 forall mu mu1 mu2 a b c u v,
 cov2_predict mu mu1 mu2 a b c u v mu1 mu2=mu.
Proof.
 intros; unfold cov2_predict; ring.
Qed.

(**
 [cov2_predict_shift_observation] (theorem) — Joint translation of an observed score and its population mean leaves the multivariate conditional prediction unchanged.
 Mathematical meaning: Joint translation of an observed score and its population mean leaves the multivariate conditional prediction unchanged.
 Exact checked proposition: forall mu mu1 mu2 a b c u v x y d, cov2_predict mu (mu1+d) mu2 a b c u v (x+d) y = cov2_predict mu mu1 mu2 a b c u v x y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_predict_shift_observation :
 forall mu mu1 mu2 a b c u v x y d,
 cov2_predict mu (mu1+d) mu2 a b c u v (x+d) y =
 cov2_predict mu mu1 mu2 a b c u v x y.
Proof.
 intros; unfold cov2_predict; ring.
Qed.

(**
 [cov2_predict_target_scale] (theorem) — The two-observation affine predictor transforms covariantly under standardized-IQ target rescaling.
 Mathematical meaning: The two-observation affine predictor transforms covariantly under standardized-IQ target rescaling.
 Exact checked proposition: forall mu mu1 mu2 a b c u v x y k, cov2_predict (k*mu) mu1 mu2 a b c (k*u) (k*v) x y = k*cov2_predict mu mu1 mu2 a b c u v x y.
 Premises and side conditions: Every nonzero determinant, positive covariance principal minor, full quadratic positivity and relevant input-mass premise is explicit in the declaration. Pure algebraic laws allow arbitrary real parameters, including degenerate covariance blocks where no inverse is taken.
 Proof/definition method: Algebraic normal equations, symmetry, covariance quadratic completion, positivity and uniqueness by standard Rocq real arithmetic; every nonzero denominator is explicit.
 Library reuse: Stdlib.Reals/Lra/Psatz/Field/Ring and existing common finite covariance/regression interpretation; no new recursive matrix operations, custom numerical optimization or postulated probability law.
 Boundary: Exact real covariance-block algebra only. Does not establish a Gaussian random vector, an L1 conditional expectation, a normal tail probability, or empirical IQ assumptions.
 *)
Theorem cov2_predict_target_scale :
 forall mu mu1 mu2 a b c u v x y k,
 cov2_predict (k*mu) mu1 mu2 a b c (k*u) (k*v) x y =
 k*cov2_predict mu mu1 mu2 a b c u v x y.
Proof.
 intros; unfold cov2_predict.
 rewrite cov2_beta_first_homogeneous.
 rewrite cov2_beta_second_homogeneous.
 ring.
Qed.

(** Continuation D026x: report-facing covariance sensitivity and strict optimization. *)

(**
 [cov2_quad_swap] (theorem) — Relabeling two tests leaves their covariance energy unchanged.
 Mathematical meaning: Relabeling two tests leaves their covariance energy unchanged.
 Exact checked proposition: forall a b c x y, cov2_quad a b c x y = cov2_quad b a c y x.
 Premises and side conditions: No positivity condition is needed; this is an identity in the real polynomial ring.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_quad_swap :
 forall a b c x y, cov2_quad a b c x y = cov2_quad b a c y x.
Proof.
 intros; unfold cov2_quad; ring.
Qed.

(**
 [cov2_quad_target_scale] (theorem) — Scaling both coefficients by the same factor scales covariance energy quadratically.
 Mathematical meaning: Scaling both coefficients by the same factor scales covariance energy quadratically.
 Exact checked proposition: forall a b c x y k, cov2_quad a b c (k*x) (k*y) = k*k*cov2_quad a b c x y.
 Premises and side conditions: Any real scale is permitted, including zero and negative scales.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_quad_target_scale :
 forall a b c x y k, cov2_quad a b c (k*x) (k*y) = k*k*cov2_quad a b c x y.
Proof.
 intros; unfold cov2_quad; ring.
Qed.

(**
 [cov2_quad_polarization] (theorem) — The cross term of two covariance-weighted score directions is an explicit bilinear pairing.
 Mathematical meaning: The cross term of two covariance-weighted score directions is an explicit bilinear pairing.
 Exact checked proposition: forall a b c x y x' y', cov2_quad a b c (x+x') (y+y') = cov2_quad a b c x y + cov2_quad a b c x' y' + 2*(a*x*x'+c*(x*y'+y*x')+b*y*y').
 Premises and side conditions: The covariance coefficients and score directions can be arbitrary real numbers.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_quad_polarization :
 forall a b c x y x' y', cov2_quad a b c (x+x') (y+y') = cov2_quad a b c x y + cov2_quad a b c x' y' + 2*(a*x*x'+c*(x*y'+y*x')+b*y*y').
Proof.
 intros; unfold cov2_quad; ring.
Qed.

(**
 [cov2_quad_parallelogram] (theorem) — The covariance quadratic form obeys the parallelogram law, allowing deterministic variance decompositions.
 Mathematical meaning: The covariance quadratic form obeys the parallelogram law, allowing deterministic variance decompositions.
 Exact checked proposition: forall a b c x y h k, cov2_quad a b c (x+h) (y+k) + cov2_quad a b c (x-h) (y-k) = 2*cov2_quad a b c x y + 2*cov2_quad a b c h k.
 Premises and side conditions: This holds algebraically even for indefinite symmetric blocks.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_quad_parallelogram :
 forall a b c x y h k, cov2_quad a b c (x+h) (y+k) + cov2_quad a b c (x-h) (y-k) = 2*cov2_quad a b c x y + 2*cov2_quad a b c h k.
Proof.
 intros; unfold cov2_quad; ring.
Qed.

(**
 [cov2_det_congruence] (theorem) — Rescaling the two observed tests changes the covariance determinant by the square of the joint scale.
 Mathematical meaning: Rescaling the two observed tests changes the covariance determinant by the square of the joint scale.
 Exact checked proposition: forall a b c k l, cov2_det (k*k*a) (l*l*b) (k*l*c) = (k*l)*(k*l)*cov2_det a b c.
 Premises and side conditions: All scales are allowed; invertibility is considered only in later corollaries.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_det_congruence :
 forall a b c k l, cov2_det (k*k*a) (l*l*b) (k*l*c) = (k*l)*(k*l)*cov2_det a b c.
Proof.
 intros; unfold cov2_det; ring.
Qed.

(**
 [cov2_quad_congruence] (theorem) — The covariance energy after changing score units equals the original energy of appropriately scaled coefficients.
 Mathematical meaning: The covariance energy after changing score units equals the original energy of appropriately scaled coefficients.
 Exact checked proposition: forall a b c x y k l, cov2_quad (k*k*a) (l*l*b) (k*l*c) x y = cov2_quad a b c (k*x) (l*y).
 Premises and side conditions: There are no division or invertibility hypotheses.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_quad_congruence :
 forall a b c x y k l, cov2_quad (k*k*a) (l*l*b) (k*l*c) x y = cov2_quad a b c (k*x) (l*y).
Proof.
 intros; unfold cov2_quad; ring.
Qed.

(**
 [cov2_risk_congruence] (theorem) — Risk computed after unit changes of both observations equals risk in the original units with correspondingly scaled prediction weights.
 Mathematical meaning: Risk computed after unit changes of both observations equals risk in the original units with correspondingly scaled prediction weights.
 Exact checked proposition: forall a b c u v s x y k l, cov2_risk (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) s x y = cov2_risk a b c u v s (k*x) (l*y).
 Premises and side conditions: This is a deterministic risk identity; no stochastic independence is assumed.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_congruence :
 forall a b c u v s x y k l, cov2_risk (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) s x y = cov2_risk a b c u v s (k*x) (l*y).
Proof.
 intros; unfold cov2_risk; rewrite cov2_quad_congruence; ring.
Qed.

(**
 [cov2_risk_swap] (theorem) — Interchanging the two observed tests leaves the full linear squared-error risk invariant.
 Mathematical meaning: Interchanging the two observed tests leaves the full linear squared-error risk invariant.
 Exact checked proposition: forall a b c u v s x y, cov2_risk a b c u v s x y = cov2_risk b a c v u s y x.
 Premises and side conditions: No assumption on the determinant is necessary for evaluating risk.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_swap :
 forall a b c u v s x y, cov2_risk a b c u v s x y = cov2_risk b a c v u s y x.
Proof.
 intros; unfold cov2_risk,cov2_quad; ring.
Qed.

(**
 [cov2_schur_swap] (theorem) — Interchanging two observed tests leaves the optimal Schur residual variance unchanged.
 Mathematical meaning: Interchanging two observed tests leaves the optimal Schur residual variance unchanged.
 Exact checked proposition: forall a b c u v s, cov2_schur a b c u v s = cov2_schur b a c v u s.
 Premises and side conditions: This equality remains true for singular blocks because the same totalized real division is used on both sides.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_swap :
 forall a b c u v s, cov2_schur a b c u v s = cov2_schur b a c v u s.
Proof.
 intros a b c u v s; unfold cov2_schur; rewrite <- (cov2_beta_swap_first a b c u v); rewrite <- (cov2_beta_swap_second a b c u v); ring.
Qed.

(**
 [cov2_predict_swap] (theorem) — The affine regression predictor is invariant under a consistent relabeling of the two observed test scores.
 Mathematical meaning: The affine regression predictor is invariant under a consistent relabeling of the two observed test scores.
 Exact checked proposition: forall mu mu1 mu2 a b c u v x y, cov2_predict mu mu1 mu2 a b c u v x y = cov2_predict mu mu2 mu1 b a c v u y x.
 Premises and side conditions: All means and scores are real; interpretation as an optimum requires invertibility.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_predict_swap :
 forall mu mu1 mu2 a b c u v x y, cov2_predict mu mu1 mu2 a b c u v x y = cov2_predict mu mu2 mu1 b a c v u y x.
Proof.
 intros mu mu1 mu2 a b c u v x y; unfold cov2_predict; rewrite <- (cov2_beta_swap_first a b c u v); rewrite <- (cov2_beta_swap_second a b c u v); ring.
Qed.

(**
 [cov2_risk_variance_shift] (theorem) — Increasing unconditional target variance by a constant increases every candidate squared-error risk by exactly that constant.
 Mathematical meaning: Increasing unconditional target variance by a constant increases every candidate squared-error risk by exactly that constant.
 Exact checked proposition: forall a b c u v s x y d, cov2_risk a b c u v (s+d) x y = cov2_risk a b c u v s x y+d.
 Premises and side conditions: The shift need not be positive for this algebraic identity.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_variance_shift :
 forall a b c u v s x y d, cov2_risk a b c u v (s+d) x y = cov2_risk a b c u v s x y+d.
Proof.
 intros; unfold cov2_risk; ring.
Qed.

(**
 [cov2_schur_variance_shift] (theorem) — A constant variance contribution unrelated to the observed scores passes unchanged through the Schur residual.
 Mathematical meaning: A constant variance contribution unrelated to the observed scores passes unchanged through the Schur residual.
 Exact checked proposition: forall a b c u v s d, cov2_schur a b c u v (s+d) = cov2_schur a b c u v s+d.
 Premises and side conditions: No singular denominator is canceled.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_variance_shift :
 forall a b c u v s d, cov2_schur a b c u v (s+d) = cov2_schur a b c u v s+d.
Proof.
 intros; unfold cov2_schur; ring.
Qed.

(**
 [cov2_risk_parallelogram] (theorem) — The sum of risks at symmetrically perturbed predictor coefficients separates baseline risk and the perturbation covariance energy.
 Mathematical meaning: The sum of risks at symmetrically perturbed predictor coefficients separates baseline risk and the perturbation covariance energy.
 Exact checked proposition: forall a b c u v s x y h k, cov2_risk a b c u v s (x+h) (y+k) + cov2_risk a b c u v s (x-h) (y-k) = 2*cov2_risk a b c u v s x y + 2*cov2_quad a b c h k.
 Premises and side conditions: This equality holds without any positivity or invertibility assumptions.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_parallelogram :
 forall a b c u v s x y h k, cov2_risk a b c u v s (x+h) (y+k) + cov2_risk a b c u v s (x-h) (y-k) = 2*cov2_risk a b c u v s x y + 2*cov2_quad a b c h k.
Proof.
 intros; unfold cov2_risk,cov2_quad; ring.
Qed.

(**
 [cov2_risk_midpoint_identity] (theorem) — The Jensen gap of quadratic prediction risk equals one-half the quadratic covariance energy of the difference between candidate coefficient vectors.
 Mathematical meaning: The Jensen gap of quadratic prediction risk equals one-half the quadratic covariance energy of the difference between candidate coefficient vectors.
 Exact checked proposition: forall a b c u v s x y x' y', 2*(cov2_risk a b c u v s x y + cov2_risk a b c u v s x' y' - 2*cov2_risk a b c u v s ((x+x')/2) ((y+y')/2)) = cov2_quad a b c (x-x') (y-y').
 Premises and side conditions: The midpoint uses division by the nonzero real constant two.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_midpoint_identity :
 forall a b c u v s x y x' y', 2*(cov2_risk a b c u v s x y + cov2_risk a b c u v s x' y' - 2*cov2_risk a b c u v s ((x+x')/2) ((y+y')/2)) = cov2_quad a b c (x-x') (y-y').
Proof.
 intros; unfold cov2_risk,cov2_quad; field; lra.
Qed.

(**
 [cov2_risk_midpoint_convex] (theorem) — Under positive-definite observed covariance, least-squares risk is convex between any pair of coefficient vectors.
 Mathematical meaning: Under positive-definite observed covariance, least-squares risk is convex between any pair of coefficient vectors.
 Exact checked proposition: forall a b c u v s x y x' y', 0<a -> 0<cov2_det a b c -> 2*cov2_risk a b c u v s ((x+x')/2) ((y+y')/2) <= cov2_risk a b c u v s x y + cov2_risk a b c u v s x' y'.
 Premises and side conditions: Both the leading variance and the determinant must be strictly positive.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_midpoint_convex :
 forall a b c u v s x y x' y', 0<a -> 0<cov2_det a b c -> 2*cov2_risk a b c u v s ((x+x')/2) ((y+y')/2) <= cov2_risk a b c u v s x y + cov2_risk a b c u v s x' y'.
Proof.
 intros a b c u v s x y x' y' Ha Hd; pose proof (cov2_risk_midpoint_identity a b c u v s x y x' y') as Hi; pose proof (cov2_quad_positive_semidefinite a b c (x-x') (y-y') Ha Hd) as Hq; lra.
Qed.

(**
 [cov2_risk_midpoint_strict] (theorem) — Positive-definite covariance makes squared-error prediction risk strictly convex for distinct predictor coefficient vectors.
 Mathematical meaning: Positive-definite covariance makes squared-error prediction risk strictly convex for distinct predictor coefficient vectors.
 Exact checked proposition: forall a b c u v s x y x' y', 0<a -> 0<cov2_det a b c -> (x<>x' \/ y<>y') -> 2*cov2_risk a b c u v s ((x+x')/2) ((y+y')/2) < cov2_risk a b c u v s x y + cov2_risk a b c u v s x' y'.
 Premises and side conditions: The coefficient pairs must differ in at least one real coordinate.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_midpoint_strict :
 forall a b c u v s x y x' y', 0<a -> 0<cov2_det a b c -> (x<>x' \/ y<>y') -> 2*cov2_risk a b c u v s ((x+x')/2) ((y+y')/2) < cov2_risk a b c u v s x y + cov2_risk a b c u v s x' y'.
Proof.
 intros a b c u v s x y x' y' Ha Hd Hneq; assert (Hdelta:x-x'<>0 \/ y-y'<>0) by (destruct Hneq; [left|right]; lra); pose proof (cov2_quad_positive_definite a b c (x-x') (y-y') Ha Hd Hdelta) as Hq; pose proof (cov2_risk_midpoint_identity a b c u v s x y x' y') as Hi; lra.
Qed.

(**
 [cov2_risk_strict_above_schur] (theorem) — Every nonoptimal pair of regression coefficients has strictly greater prediction risk than the Schur-optimal pair.
 Mathematical meaning: Every nonoptimal pair of regression coefficients has strictly greater prediction risk than the Schur-optimal pair.
 Exact checked proposition: forall a b c u v s x y, 0<a -> 0<cov2_det a b c -> (x<>cov2_beta_first a b c u v \/ y<>cov2_beta_second a b c u v) -> cov2_schur a b c u v s < cov2_risk a b c u v s x y.
 Premises and side conditions: Positive definiteness and a nonzero coefficient error are essential for strictness.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_strict_above_schur :
 forall a b c u v s x y, 0<a -> 0<cov2_det a b c -> (x<>cov2_beta_first a b c u v \/ y<>cov2_beta_second a b c u v) -> cov2_schur a b c u v s < cov2_risk a b c u v s x y.
Proof.
 intros a b c u v s x y Ha Hd Hneq; pose proof (cov2_risk_completed_square a b c u v s x y ltac:(lra)) as Hr; assert (Hdelta:x-cov2_beta_first a b c u v<>0 \/ y-cov2_beta_second a b c u v<>0) by (destruct Hneq; [left|right]; lra); pose proof (cov2_quad_positive_definite a b c (x-cov2_beta_first a b c u v) (y-cov2_beta_second a b c u v) Ha Hd Hdelta) as Hp; lra.
Qed.

(**
 [cov2_risk_optimal_iff] (theorem) — Equality with minimum prediction risk characterizes exactly the unique simultaneous normal-equation coefficients.
 Mathematical meaning: Equality with minimum prediction risk characterizes exactly the unique simultaneous normal-equation coefficients.
 Exact checked proposition: forall a b c u v s x y, 0<a -> 0<cov2_det a b c -> (cov2_risk a b c u v s x y = cov2_schur a b c u v s <-> x=cov2_beta_first a b c u v /\ y=cov2_beta_second a b c u v).
 Premises and side conditions: The covariance block is positive definite, excluding nonunique minima.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_optimal_iff :
 forall a b c u v s x y, 0<a -> 0<cov2_det a b c -> (cov2_risk a b c u v s x y = cov2_schur a b c u v s <-> x=cov2_beta_first a b c u v /\ y=cov2_beta_second a b c u v).
Proof.
 intros a b c u v s x y Ha Hd; split.
 - intro Hr; exact (cov2_risk_unique_minimizer a b c u v s x y Ha Hd Hr).
 - intros [Hx Hy]; subst x y; apply cov2_risk_at_optimum; lra.
Qed.

(**
 [cov2_schur_second_observation_bound] (theorem) — Adding the first observation cannot worsen optimal prediction relative to using the second observation alone.
 Mathematical meaning: Adding the first observation cannot worsen optimal prediction relative to using the second observation alone.
 Exact checked proposition: forall a b c u v s, 0<b -> 0<cov2_det a b c -> cov2_schur a b c u v s <= cov2_one_risk b v s.
 Premises and side conditions: The second observed variance and common determinant must be strictly positive.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_second_observation_bound :
 forall a b c u v s, 0<b -> 0<cov2_det a b c -> cov2_schur a b c u v s <= cov2_one_risk b v s.
Proof.
 intros a b c u v s Hb Hd; rewrite cov2_schur_swap; apply cov2_two_obs_improves_one; [exact Hb|rewrite <- cov2_det_symmetric; exact Hd].
Qed.

(**
 [cov2_schur_second_strict_gain] (theorem) — The first test strictly improves on using only the second if its residual target covariance is nonzero.
 Mathematical meaning: The first test strictly improves on using only the second if its residual target covariance is nonzero.
 Exact checked proposition: forall a b c u v s, 0<b -> 0<cov2_det a b c -> b*u<>c*v -> cov2_schur a b c u v s < cov2_one_risk b v s.
 Premises and side conditions: Strict improvement requires a nonzero partial target covariance and positive covariance minors.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_second_strict_gain :
 forall a b c u v s, 0<b -> 0<cov2_det a b c -> b*u<>c*v -> cov2_schur a b c u v s < cov2_one_risk b v s.
Proof.
 intros a b c u v s Hb Hd Hpartial; rewrite cov2_schur_swap; apply cov2_strict_information_gain; [exact Hb|rewrite <- cov2_det_symmetric; exact Hd|exact Hpartial].
Qed.

(**
 [cov2_schur_second_no_gain_iff] (theorem) — The first test provides no extra linear information given the second precisely when its partial target covariance vanishes.
 Mathematical meaning: The first test provides no extra linear information given the second precisely when its partial target covariance vanishes.
 Exact checked proposition: forall a b c u v s, 0<b -> 0<cov2_det a b c -> (cov2_schur a b c u v s = cov2_one_risk b v s <-> b*u=c*v).
 Premises and side conditions: Both positive-definiteness premises are needed for the equivalence.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_second_no_gain_iff :
 forall a b c u v s, 0<b -> 0<cov2_det a b c -> (cov2_schur a b c u v s = cov2_one_risk b v s <-> b*u=c*v).
Proof.
 intros a b c u v s Hb Hd; rewrite cov2_schur_swap; apply cov2_no_additional_gain_iff; [exact Hb|rewrite <- cov2_det_symmetric; exact Hd].
Qed.

(**
 [cov2_schur_both_one_score_bounds] (theorem) — Optimal two-test prediction is never inferior to either separate one-test predictor.
 Mathematical meaning: Optimal two-test prediction is never inferior to either separate one-test predictor.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<b -> 0<cov2_det a b c -> cov2_schur a b c u v s <= cov2_one_risk a u s /\ cov2_schur a b c u v s <= cov2_one_risk b v s.
 Premises and side conditions: Both observed variances and the covariance determinant are strictly positive.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_both_one_score_bounds :
 forall a b c u v s, 0<a -> 0<b -> 0<cov2_det a b c -> cov2_schur a b c u v s <= cov2_one_risk a u s /\ cov2_schur a b c u v s <= cov2_one_risk b v s.
Proof.
 intros a b c u v s Ha Hb Hd; split; [apply cov2_two_obs_improves_one|apply cov2_schur_second_observation_bound]; assumption.
Qed.

(**
 [cov2_schur_unconditional_eq_iff] (theorem) — The optimal two-test residual variance equals unconditional variance exactly when both observed tests carry zero target covariance.
 Mathematical meaning: The optimal two-test residual variance equals unconditional variance exactly when both observed tests carry zero target covariance.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> (cov2_schur a b c u v s=s <-> u=0 /\ v=0).
 Premises and side conditions: The observed covariance block must be positive definite for zero explained variance to force both cross-covariances to vanish.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_unconditional_eq_iff :
 forall a b c u v s, 0<a -> 0<cov2_det a b c -> (cov2_schur a b c u v s=s <-> u=0 /\ v=0).
Proof.
 intros a b c u v s Ha Hd; split; intro H; [|destruct H as [Hu Hv]; subst u v; unfold cov2_schur,cov2_beta_first,cov2_beta_second,Rdiv; ring]; pose proof (cov2_beta_explained_quadratic a b c u v ltac:(lra)) as He; assert (Hq:cov2_quad a b c (cov2_beta_first a b c u v) (cov2_beta_second a b c u v)=0) by (unfold cov2_schur in H; lra); apply (proj1 (cov2_quad_zero_iff a b c _ _ Ha Hd)) in Hq; destruct Hq as [Hp Hq]; pose proof (cov2_beta_first_normal_equation a b c u v ltac:(lra)) as H1; pose proof (cov2_beta_second_normal_equation a b c u v ltac:(lra)) as H2; rewrite Hp,Hq in H1,H2; split; nra.
Qed.

(**
 [cov2_schur_unconditional_strict_gain] (theorem) — Any nonzero linear covariance signal in either test strictly reduces best linear residual variance below unconditional target variance.
 Mathematical meaning: Any nonzero linear covariance signal in either test strictly reduces best linear residual variance below unconditional target variance.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> (u<>0 \/ v<>0) -> cov2_schur a b c u v s<s.
 Premises and side conditions: Requires positive definiteness and at least one nonzero target/test covariance.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_unconditional_strict_gain :
 forall a b c u v s, 0<a -> 0<cov2_det a b c -> (u<>0 \/ v<>0) -> cov2_schur a b c u v s<s.
Proof.
 intros a b c u v s Ha Hd Hsignal; pose proof (cov2_schur_le_unconditional a b c u v s Ha Hd) as Hle; assert (Hneq:cov2_schur a b c u v s<>s) by (intro He; pose proof ((proj1 (cov2_schur_unconditional_eq_iff a b c u v s Ha Hd)) He) as [Hu Hv]; destruct Hsignal as [H|H]; contradiction); lra.
Qed.

(**
 [cov2_risk_signal_reflection] (theorem) — Simultaneously negating target covariances and prediction weights leaves the quadratic risk invariant.
 Mathematical meaning: Simultaneously negating target covariances and prediction weights leaves the quadratic risk invariant.
 Exact checked proposition: forall a b c u v s x y, cov2_risk a b c (-u) (-v) s (-x) (-y) = cov2_risk a b c u v s x y.
 Premises and side conditions: This algebraic symmetry does not require positive covariance.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_risk_signal_reflection :
 forall a b c u v s x y, cov2_risk a b c (-u) (-v) s (-x) (-y) = cov2_risk a b c u v s x y.
Proof.
 intros; unfold cov2_risk,cov2_quad; ring.
Qed.

(**
 [cov2_predict_shift_second] (theorem) — Translating the second test and its mean by the same amount does not change the affine regression prediction.
 Mathematical meaning: Translating the second test and its mean by the same amount does not change the affine regression prediction.
 Exact checked proposition: forall mu mu1 mu2 a b c u v x y d, cov2_predict mu mu1 (mu2+d) a b c u v x (y+d) = cov2_predict mu mu1 mu2 a b c u v x y.
 Premises and side conditions: The observed score and its reference mean must be translated together.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_predict_shift_second :
 forall mu mu1 mu2 a b c u v x y d, cov2_predict mu mu1 (mu2+d) a b c u v x (y+d) = cov2_predict mu mu1 mu2 a b c u v x y.
Proof.
 intros; unfold cov2_predict; ring.
Qed.

(**
 [cov2_predict_target_translation] (theorem) — Translating the target mean translates its affine multivariate predictor by exactly the same amount.
 Mathematical meaning: Translating the target mean translates its affine multivariate predictor by exactly the same amount.
 Exact checked proposition: forall mu mu1 mu2 a b c u v x y d, cov2_predict (mu+d) mu1 mu2 a b c u v x y = cov2_predict mu mu1 mu2 a b c u v x y+d.
 Premises and side conditions: No change in covariance or observed-score centering is assumed.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_predict_target_translation :
 forall mu mu1 mu2 a b c u v x y d, cov2_predict (mu+d) mu1 mu2 a b c u v x y = cov2_predict mu mu1 mu2 a b c u v x y+d.
Proof.
 intros; unfold cov2_predict; ring.
Qed.

(**
 [cov2_beta_congruence_first] (theorem) — The first regression coefficient transforms contravariantly under independent changes of observed-score units.
 Mathematical meaning: The first regression coefficient transforms contravariantly under independent changes of observed-score units.
 Exact checked proposition: forall a b c u v k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> k*cov2_beta_first (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) = cov2_beta_first a b c u v.
 Premises and side conditions: Both test-unit scales and the original covariance determinant must be nonzero.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_beta_congruence_first :
 forall a b c u v k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> k*cov2_beta_first (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) = cov2_beta_first a b c u v.
Proof.
 intros a b c u v k l Hk Hl Hd; unfold cov2_beta_first; rewrite cov2_det_congruence; unfold Rdiv; field; nra.
Qed.

(**
 [cov2_beta_congruence_second] (theorem) — The second regression coefficient transforms contravariantly under independent changes of observed-score units.
 Mathematical meaning: The second regression coefficient transforms contravariantly under independent changes of observed-score units.
 Exact checked proposition: forall a b c u v k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> l*cov2_beta_second (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) = cov2_beta_second a b c u v.
 Premises and side conditions: Both test-unit scales and the original covariance determinant must be nonzero.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_beta_congruence_second :
 forall a b c u v k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> l*cov2_beta_second (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) = cov2_beta_second a b c u v.
Proof.
 intros a b c u v k l Hk Hl Hd; unfold cov2_beta_second; rewrite cov2_det_congruence; unfold Rdiv; field; nra.
Qed.

(**
 [cov2_schur_congruence] (theorem) — The optimal two-test residual variance is invariant under arbitrary nonzero changes of measurement units for the two tests.
 Mathematical meaning: The optimal two-test residual variance is invariant under arbitrary nonzero changes of measurement units for the two tests.
 Exact checked proposition: forall a b c u v s k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> cov2_schur (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) s = cov2_schur a b c u v s.
 Premises and side conditions: Changes of score units must be invertible; a nonzero determinant is necessary for the regression formulas.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_schur_congruence :
 forall a b c u v s k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> cov2_schur (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) s = cov2_schur a b c u v s.
Proof.
 intros a b c u v s k l Hk Hl Hd; unfold cov2_schur; replace (k*u*cov2_beta_first (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v)) with (u*(k*cov2_beta_first (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v))) by ring; replace (l*v*cov2_beta_second (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v)) with (v*(l*cov2_beta_second (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v))) by ring; rewrite (cov2_beta_congruence_first a b c u v k l Hk Hl Hd); rewrite (cov2_beta_congruence_second a b c u v k l Hk Hl Hd); reflexivity.
Qed.

(**
 [cov2_predict_congruence] (theorem) — An affine two-test predictor is unchanged when both observed scores, their means, and all covariance inputs are converted consistently to new units.
 Mathematical meaning: An affine two-test predictor is unchanged when both observed scores, their means, and all covariance inputs are converted consistently to new units.
 Exact checked proposition: forall mu mu1 mu2 a b c u v x y k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> cov2_predict mu (k*mu1) (l*mu2) (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) (k*x) (l*y) = cov2_predict mu mu1 mu2 a b c u v x y.
 Premises and side conditions: Scales must be nonzero and the covariance block invertible; this is predictor algebra, not Gaussian conditioning.
 Proof/definition method: Reuse preceding covariance, regression and positivity lemmas, together with Rocq's trusted real-algebra tactics; no new matrix or probability operators are introduced.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring and Field, with the already-kernel-checked TwoObservationSchur theorems rather than duplicated specialized derivations.
 Boundary: Exact finite-dimensional real covariance and best linear-prediction algebra only; does not assert Gaussian conditional laws, continuous normal tails, or empirical IQ-model validity.
 *)
Theorem cov2_predict_congruence :
 forall mu mu1 mu2 a b c u v x y k l, k<>0 -> l<>0 -> cov2_det a b c<>0 -> cov2_predict mu (k*mu1) (l*mu2) (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v) (k*x) (l*y) = cov2_predict mu mu1 mu2 a b c u v x y.
Proof.
 intros mu mu1 mu2 a b c u v x y k l Hk Hl Hd; unfold cov2_predict; replace (cov2_beta_first (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v)*(k*x-k*mu1)) with ((k*cov2_beta_first (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v))*(x-mu1)) by ring; replace (cov2_beta_second (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v)*(l*y-l*mu2)) with ((l*cov2_beta_second (k*k*a) (l*l*b) (k*l*c) (k*u) (l*v))*(y-mu2)) by ring; rewrite (cov2_beta_congruence_first a b c u v k l Hk Hl Hd); rewrite (cov2_beta_congruence_second a b c u v k l Hk Hl Hd); reflexivity.
Qed.


(* D029x: innovation partial-regression algebra, correlated score sensitivity,
   and independent-diagonal-noise monotonicity for the report's regression formulas. *)

(**
 [cov2_innovation_variance] (definition) — Residual variance of observation two after linearly projecting it onto observation one.
 Mathematical meaning: Residual variance of observation two after linearly projecting it onto observation one.
 Exact declaration: Definition cov2_innovation_variance (a b c:R) : R := b-c*c/a.
 Premises and side conditions: Requires the stated real-valued covariance parameters; residualized statistical interpretation presumes nonzero/positive first-test variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Definition cov2_innovation_variance (a b c:R) : R := b-c*c/a.

(**
 [cov2_innovation_covariance] (definition) — Residual target/second-observation covariance after partialing out observation one.
 Mathematical meaning: Residual target/second-observation covariance after partialing out observation one.
 Exact declaration: Definition cov2_innovation_covariance (a c u v:R) : R := v-c*u/a.
 Premises and side conditions: Requires the stated real-valued covariance parameters; residualized statistical interpretation presumes nonzero/positive first-test variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Definition cov2_innovation_covariance (a c u v:R) : R := v-c*u/a.

(**
 [cov2_innovation_gain] (definition) — Incremental linear prediction information from the second residualized observation.
 Mathematical meaning: Incremental linear prediction information from the second residualized observation.
 Exact declaration: Definition cov2_innovation_gain (a b c u v:R) : R := cov2_innovation_covariance a c u v * cov2_innovation_covariance a c u v / cov2_innovation_variance a b c.
 Premises and side conditions: Requires the stated real-valued covariance parameters; residualized statistical interpretation presumes nonzero/positive first-test variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Definition cov2_innovation_gain (a b c u v:R) : R := cov2_innovation_covariance a c u v * cov2_innovation_covariance a c u v / cov2_innovation_variance a b c.

(**
 [cov2_innovation_variance_times_first] (theorem) — The innovation variance times the first test variance equals the two-test covariance determinant.
 Mathematical meaning: The innovation variance times the first test variance equals the two-test covariance determinant.
 Exact checked proposition: forall a b c, a<>0 -> a*cov2_innovation_variance a b c=cov2_det a b c.
 Premises and side conditions: Requires a nonzero first observation variance, so residualization is well-defined.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_times_first :
 forall a b c, a<>0 -> a*cov2_innovation_variance a b c=cov2_det a b c.
Proof.
 intros a b c Ha; unfold cov2_innovation_variance,cov2_det; field; exact Ha.
Qed.

(**
 [cov2_innovation_variance_ratio] (theorem) — The innovation variance equals the Schur determinant divided by the first test variance.
 Mathematical meaning: The innovation variance equals the Schur determinant divided by the first test variance.
 Exact checked proposition: forall a b c, a<>0 -> cov2_innovation_variance a b c=cov2_det a b c/a.
 Premises and side conditions: Assumes invertible first-test marginal variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_ratio :
 forall a b c, a<>0 -> cov2_innovation_variance a b c=cov2_det a b c/a.
Proof.
 intros a b c Ha; unfold cov2_innovation_variance,cov2_det; field; exact Ha.
Qed.

(**
 [cov2_innovation_variance_positive] (theorem) — Strictly positive definite observed covariance implies strictly positive second-test innovation variance.
 Mathematical meaning: Strictly positive definite observed covariance implies strictly positive second-test innovation variance.
 Exact checked proposition: forall a b c, 0<a -> 0<cov2_det a b c -> 0<cov2_innovation_variance a b c.
 Premises and side conditions: Requires first variance and covariance determinant strictly positive.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_positive :
 forall a b c, 0<a -> 0<cov2_det a b c -> 0<cov2_innovation_variance a b c.
Proof.
 intros a b c Ha Hd; pose proof (cov2_innovation_variance_times_first a b c ltac:(lra)) as He; nra.
Qed.

(**
 [cov2_innovation_variance_nonnegative] (theorem) — A nonnegative covariance determinant with positive first-test variance yields nonnegative residual innovation variance.
 Mathematical meaning: A nonnegative covariance determinant with positive first-test variance yields nonnegative residual innovation variance.
 Exact checked proposition: forall a b c, 0<a -> 0<=cov2_det a b c -> 0<=cov2_innovation_variance a b c.
 Premises and side conditions: Positive first marginal and nonnegative determinant are assumed.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_nonnegative :
 forall a b c, 0<a -> 0<=cov2_det a b c -> 0<=cov2_innovation_variance a b c.
Proof.
 intros a b c Ha Hd; pose proof (cov2_innovation_variance_times_first a b c ltac:(lra)) as He; nra.
Qed.

(**
 [cov2_innovation_variance_zero_iff] (theorem) — At positive first-test variance, zero innovation variance is equivalent to a singular observed covariance block.
 Mathematical meaning: At positive first-test variance, zero innovation variance is equivalent to a singular observed covariance block.
 Exact checked proposition: forall a b c, 0<a -> (cov2_innovation_variance a b c=0 <-> cov2_det a b c=0).
 Premises and side conditions: Positive first variance ensures that multiplication is reversible.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_zero_iff :
 forall a b c, 0<a -> (cov2_innovation_variance a b c=0 <-> cov2_det a b c=0).
Proof.
 intros a b c Ha; pose proof (cov2_innovation_variance_times_first a b c ltac:(lra)) as He; split; intro H; nra.
Qed.

(**
 [cov2_innovation_variance_noise_shift] (theorem) — Adding independent measurement variance to the second test increases its residual innovation variance by exactly that amount.
 Mathematical meaning: Adding independent measurement variance to the second test increases its residual innovation variance by exactly that amount.
 Exact checked proposition: forall a b c t, cov2_innovation_variance a (b+t) c=cov2_innovation_variance a b c+t.
 Premises and side conditions: An additive t is a modeled variance perturbation; no distributional independence theorem is asserted.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_noise_shift :
 forall a b c t, cov2_innovation_variance a (b+t) c=cov2_innovation_variance a b c+t.
Proof.
 intros; unfold cov2_innovation_variance; ring.
Qed.

(**
 [cov2_innovation_variance_noise_monotone] (theorem) — Nonnegative additional second-test measurement noise cannot reduce the residual innovation variance.
 Mathematical meaning: Nonnegative additional second-test measurement noise cannot reduce the residual innovation variance.
 Exact checked proposition: forall a b c t, 0<=t -> cov2_innovation_variance a b c<=cov2_innovation_variance a (b+t) c.
 Premises and side conditions: Assumes nonnegative added variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_noise_monotone :
 forall a b c t, 0<=t -> cov2_innovation_variance a b c<=cov2_innovation_variance a (b+t) c.
Proof.
 intros a b c t Ht; rewrite cov2_innovation_variance_noise_shift; lra.
Qed.

(**
 [cov2_innovation_variance_noise_strict] (theorem) — Strictly positive second-test noise strictly increases its innovation variance.
 Mathematical meaning: Strictly positive second-test noise strictly increases its innovation variance.
 Exact checked proposition: forall a b c t, 0<t -> cov2_innovation_variance a b c<cov2_innovation_variance a (b+t) c.
 Premises and side conditions: Assumes positive independent measurement-noise variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_variance_noise_strict :
 forall a b c t, 0<t -> cov2_innovation_variance a b c<cov2_innovation_variance a (b+t) c.
Proof.
 intros a b c t Ht; rewrite cov2_innovation_variance_noise_shift; lra.
Qed.

(**
 [cov2_innovation_covariance_times_first] (theorem) — The innovation target covariance times first-test variance equals the partial-covariance numerator.
 Mathematical meaning: The innovation target covariance times first-test variance equals the partial-covariance numerator.
 Exact checked proposition: forall a c u v, a<>0 -> a*cov2_innovation_covariance a c u v=a*v-c*u.
 Premises and side conditions: The observed first-test variance is nonzero.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_covariance_times_first :
 forall a c u v, a<>0 -> a*cov2_innovation_covariance a c u v=a*v-c*u.
Proof.
 intros a c u v Ha; unfold cov2_innovation_covariance; field; exact Ha.
Qed.

(**
 [cov2_innovation_covariance_ratio] (theorem) — Residual target covariance is the partial numerator divided by the first observed variance.
 Mathematical meaning: Residual target covariance is the partial numerator divided by the first observed variance.
 Exact checked proposition: forall a c u v, a<>0 -> cov2_innovation_covariance a c u v=(a*v-c*u)/a.
 Premises and side conditions: Requires invertibility of the first marginal covariance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_covariance_ratio :
 forall a c u v, a<>0 -> cov2_innovation_covariance a c u v=(a*v-c*u)/a.
Proof.
 intros a c u v Ha; unfold cov2_innovation_covariance; field; exact Ha.
Qed.

(**
 [cov2_innovation_covariance_zero_iff] (theorem) — The second observation contributes no residual target signal exactly when the partial covariance numerator vanishes.
 Mathematical meaning: The second observation contributes no residual target signal exactly when the partial covariance numerator vanishes.
 Exact checked proposition: forall a c u v, a<>0 -> (cov2_innovation_covariance a c u v=0 <-> a*v=c*u).
 Premises and side conditions: Nonzero first marginal variance is required; no normal-law assumption.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_covariance_zero_iff :
 forall a c u v, a<>0 -> (cov2_innovation_covariance a c u v=0 <-> a*v=c*u).
Proof.
 intros a c u v Ha; pose proof (cov2_innovation_covariance_times_first a c u v Ha) as He; split; intro H; nra.
Qed.

(**
 [cov2_innovation_covariance_additive] (theorem) — Partial covariance is additive for sums of two distinct target signals.
 Mathematical meaning: Partial covariance is additive for sums of two distinct target signals.
 Exact checked proposition: forall a c u v p q, cov2_innovation_covariance a c (u+p) (v+q)=cov2_innovation_covariance a c u v+cov2_innovation_covariance a c p q.
 Premises and side conditions: Linear covariance algebra with no positivity assumptions.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_covariance_additive :
 forall a c u v p q, cov2_innovation_covariance a c (u+p) (v+q)=cov2_innovation_covariance a c u v+cov2_innovation_covariance a c p q.
Proof.
 intros; unfold cov2_innovation_covariance,Rdiv; ring.
Qed.

(**
 [cov2_innovation_covariance_homogeneous] (theorem) — Scaling both target/test covariance coordinates scales their residual signal by the same coefficient.
 Mathematical meaning: Scaling both target/test covariance coordinates scales their residual signal by the same coefficient.
 Exact checked proposition: forall a c u v k, cov2_innovation_covariance a c (k*u) (k*v)=k*cov2_innovation_covariance a c u v.
 Premises and side conditions: Exact scalar algebra; any real multiplier is allowed.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_covariance_homogeneous :
 forall a c u v k, cov2_innovation_covariance a c (k*u) (k*v)=k*cov2_innovation_covariance a c u v.
Proof.
 intros; unfold cov2_innovation_covariance,Rdiv; ring.
Qed.

(**
 [cov2_innovation_covariance_second_units] (theorem) — Rescaling the second observation together with its target covariance scales the innovation covariance consistently.
 Mathematical meaning: Rescaling the second observation together with its target covariance scales the innovation covariance consistently.
 Exact checked proposition: forall a c u v k, cov2_innovation_covariance a (k*c) u (k*v)=k*cov2_innovation_covariance a c u v.
 Premises and side conditions: Covariance entries and units must be transformed consistently.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_covariance_second_units :
 forall a c u v k, cov2_innovation_covariance a (k*c) u (k*v)=k*cov2_innovation_covariance a c u v.
Proof.
 intros; unfold cov2_innovation_covariance,Rdiv; ring.
Qed.

(**
 [cov2_innovation_covariance_first_projection_invariance] (theorem) — Adding any multiple of the first observed test to the second target signal leaves the second partial covariance unchanged.
 Mathematical meaning: Adding any multiple of the first observed test to the second target signal leaves the second partial covariance unchanged.
 Exact checked proposition: forall a c u v k, a<>0 -> cov2_innovation_covariance a c (u+k*a) (v+k*c)=cov2_innovation_covariance a c u v.
 Premises and side conditions: First observation variance must be nonzero.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_covariance_first_projection_invariance :
 forall a c u v k, a<>0 -> cov2_innovation_covariance a c (u+k*a) (v+k*c)=cov2_innovation_covariance a c u v.
Proof.
 intros a c u v k Ha; unfold cov2_innovation_covariance; field; exact Ha.
Qed.

(**
 [cov2_beta_second_from_innovation] (theorem) — The optimal second-test regression coefficient is the innovation signal divided by its residual variance.
 Mathematical meaning: The optimal second-test regression coefficient is the innovation signal divided by its residual variance.
 Exact checked proposition: forall a b c u v, a<>0 -> cov2_det a b c<>0 -> cov2_beta_second a b c u v = cov2_innovation_covariance a c u v / cov2_innovation_variance a b c.
 Premises and side conditions: Both the first variance and full covariance determinant are nonzero.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_second_from_innovation :
 forall a b c u v, a<>0 -> cov2_det a b c<>0 -> cov2_beta_second a b c u v = cov2_innovation_covariance a c u v / cov2_innovation_variance a b c.
Proof.
 intros a b c u v Ha Hd.
 assert (Hvar:cov2_innovation_variance a b c<>0).
 { pose proof (cov2_innovation_variance_times_first a b c Ha) as He; nra. }
 unfold cov2_beta_second,cov2_innovation_covariance,
   cov2_innovation_variance,cov2_det in *.
 field; nra.
Qed.

(**
 [cov2_beta_second_zero_iff_innovation] (theorem) — The second optimal regression weight vanishes exactly when its residualized target covariance is zero.
 Mathematical meaning: The second optimal regression weight vanishes exactly when its residualized target covariance is zero.
 Exact checked proposition: forall a b c u v, 0<a -> 0<cov2_det a b c -> (cov2_beta_second a b c u v=0 <-> cov2_innovation_covariance a c u v=0).
 Premises and side conditions: Strict positive definiteness makes the innovation division nondegenerate.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_second_zero_iff_innovation :
 forall a b c u v, 0<a -> 0<cov2_det a b c -> (cov2_beta_second a b c u v=0 <-> cov2_innovation_covariance a c u v=0).
Proof.
 intros a b c u v Ha Hd.
 rewrite (cov2_beta_second_from_innovation a b c u v ltac:(lra) ltac:(lra)).
 pose proof (cov2_innovation_variance_positive a b c Ha Hd) as Hv.
 unfold Rdiv.
 assert (Hi:0< /cov2_innovation_variance a b c)
   by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H.
 - apply Rmult_integral in H.
   destruct H as [Hz|Hinv]; [exact Hz|lra].
 - rewrite H; ring.
Qed.

(**
 [cov2_beta_second_positive_iff_innovation] (theorem) — A positive second regression weight is equivalent to a positive residual target/test covariance.
 Mathematical meaning: A positive second regression weight is equivalent to a positive residual target/test covariance.
 Exact checked proposition: forall a b c u v, 0<a -> 0<cov2_det a b c -> (0<cov2_beta_second a b c u v <-> 0<cov2_innovation_covariance a c u v).
 Premises and side conditions: Both covariance minors must be positive.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_second_positive_iff_innovation :
 forall a b c u v, 0<a -> 0<cov2_det a b c -> (0<cov2_beta_second a b c u v <-> 0<cov2_innovation_covariance a c u v).
Proof.
 intros a b c u v Ha Hd.
 rewrite (cov2_beta_second_from_innovation a b c u v ltac:(lra) ltac:(lra)).
 pose proof (cov2_innovation_variance_positive a b c Ha Hd) as Hv.
 unfold Rdiv; assert (Hi:0< /cov2_innovation_variance a b c) by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H; nra.
Qed.

(**
 [cov2_beta_second_negative_iff_innovation] (theorem) — A negative second regression weight is equivalent to a negative residual target/test covariance.
 Mathematical meaning: A negative second regression weight is equivalent to a negative residual target/test covariance.
 Exact checked proposition: forall a b c u v, 0<a -> 0<cov2_det a b c -> (cov2_beta_second a b c u v<0 <-> cov2_innovation_covariance a c u v<0).
 Premises and side conditions: Both positive-definite covariance premises are explicit.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_second_negative_iff_innovation :
 forall a b c u v, 0<a -> 0<cov2_det a b c -> (cov2_beta_second a b c u v<0 <-> cov2_innovation_covariance a c u v<0).
Proof.
 intros a b c u v Ha Hd.
 rewrite (cov2_beta_second_from_innovation a b c u v ltac:(lra) ltac:(lra)).
 pose proof (cov2_innovation_variance_positive a b c Ha Hd) as Hv.
 unfold Rdiv; assert (Hi:0< /cov2_innovation_variance a b c) by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H; nra.
Qed.

(**
 [cov2_beta_first_after_partialing] (theorem) — The first regression coefficient equals the one-test coefficient corrected for the second regression weight's covariance with test one.
 Mathematical meaning: The first regression coefficient equals the one-test coefficient corrected for the second regression weight's covariance with test one.
 Exact checked proposition: forall a b c u v, a<>0 -> cov2_det a b c<>0 -> cov2_beta_first a b c u v = (u-c*cov2_beta_second a b c u v)/a.
 Premises and side conditions: Uses the first normal equation and nonzero first-test variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_first_after_partialing :
 forall a b c u v, a<>0 -> cov2_det a b c<>0 -> cov2_beta_first a b c u v = (u-c*cov2_beta_second a b c u v)/a.
Proof.
 intros a b c u v Ha Hd.
 (* The normal equations certify this identity; the explicit field
    normalization verifies both inverse denominators with the premises. *)
 unfold cov2_beta_first,cov2_beta_second,cov2_det in *.
 field; nra.
Qed.

(**
 [cov2_innovation_gain_partial_rational] (theorem) — Incremental information is the squared partial-covariance numerator divided by the positive block determinant and first variance.
 Mathematical meaning: Incremental information is the squared partial-covariance numerator divided by the positive block determinant and first variance.
 Exact checked proposition: forall a b c u v, a<>0 -> cov2_det a b c<>0 -> cov2_innovation_gain a b c u v=(a*v-c*u)*(a*v-c*u)/(a*cov2_det a b c).
 Premises and side conditions: Requires invertible first marginal and observed covariance determinant.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_partial_rational :
 forall a b c u v, a<>0 -> cov2_det a b c<>0 -> cov2_innovation_gain a b c u v=(a*v-c*u)*(a*v-c*u)/(a*cov2_det a b c).
Proof.
 intros a b c u v Ha Hd.
 assert (Hvar:cov2_innovation_variance a b c<>0).
 { pose proof (cov2_innovation_variance_times_first a b c Ha) as He; nra. }
 unfold cov2_innovation_gain,cov2_innovation_covariance,
   cov2_innovation_variance,cov2_det in *.
 field; nra.
Qed.

(**
 [cov2_innovation_gain_nonnegative] (theorem) — With positive-definite observed covariance the incremental value of the second score is nonnegative.
 Mathematical meaning: With positive-definite observed covariance the incremental value of the second score is nonnegative.
 Exact checked proposition: forall a b c u v, 0<a -> 0<cov2_det a b c -> 0<=cov2_innovation_gain a b c u v.
 Premises and side conditions: Positive observed covariance block ensures the innovation variance is positive.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_nonnegative :
 forall a b c u v, 0<a -> 0<cov2_det a b c -> 0<=cov2_innovation_gain a b c u v.
Proof.
 intros a b c u v Ha Hd.
 pose proof (cov2_innovation_variance_positive a b c Ha Hd) as Hv.
 unfold cov2_innovation_gain,Rdiv.
 assert (Hi:0<=/cov2_innovation_variance a b c) by (apply Rlt_le,Rinv_0_lt_compat; exact Hv).
 assert (Hs:0<=cov2_innovation_covariance a c u v * cov2_innovation_covariance a c u v) by nra.
 apply Rmult_le_pos; assumption.
Qed.

(**
 [cov2_innovation_gain_zero_iff] (theorem) — A residualized score has exactly zero predictive value if and only if its target covariance is zero.
 Mathematical meaning: A residualized score has exactly zero predictive value if and only if its target covariance is zero.
 Exact checked proposition: forall a b c u v, 0<a -> 0<cov2_det a b c -> (cov2_innovation_gain a b c u v=0 <-> cov2_innovation_covariance a c u v=0).
 Premises and side conditions: Positive innovation variance removes the denominator-degeneracy ambiguity.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_zero_iff :
 forall a b c u v, 0<a -> 0<cov2_det a b c -> (cov2_innovation_gain a b c u v=0 <-> cov2_innovation_covariance a c u v=0).
Proof.
 intros a b c u v Ha Hd.
 pose proof (cov2_innovation_variance_positive a b c Ha Hd) as Hv.
 unfold cov2_innovation_gain,Rdiv.
 assert (Hi:0< /cov2_innovation_variance a b c)
   by (apply Rinv_0_lt_compat; exact Hv).
 split; intro H.
 - apply Rmult_integral in H.
   destruct H as [Hsq|Hinv].
   + apply Rmult_integral in Hsq; tauto.
   + lra.
 - rewrite H; ring.
Qed.

(**
 [cov2_innovation_gain_positive_iff] (theorem) — Strictly positive incremental prediction information is equivalent to nonzero residual signal.
 Mathematical meaning: Strictly positive incremental prediction information is equivalent to nonzero residual signal.
 Exact checked proposition: forall a b c u v, 0<a -> 0<cov2_det a b c -> (0<cov2_innovation_gain a b c u v <-> cov2_innovation_covariance a c u v<>0).
 Premises and side conditions: Requires strictly positive innovation variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_positive_iff :
 forall a b c u v, 0<a -> 0<cov2_det a b c -> (0<cov2_innovation_gain a b c u v <-> cov2_innovation_covariance a c u v<>0).
Proof.
 intros a b c u v Ha Hd.
 pose proof (cov2_innovation_variance_positive a b c Ha Hd) as Hv.
 unfold cov2_innovation_gain,Rdiv.
 assert (Hi:0< /cov2_innovation_variance a b c)
   by (apply Rinv_0_lt_compat; exact Hv).
 split.
 - intro H; intro Hz; rewrite Hz in H; nra.
 - intro Hz.
   assert (Hsq:0<cov2_innovation_covariance a c u v *
                  cov2_innovation_covariance a c u v) by nra.
   apply Rmult_lt_0_compat; assumption.
Qed.

(**
 [cov2_innovation_gain_target_scale] (theorem) — A uniform scaling of target/test covariances scales the incremental explained variance quadratically.
 Mathematical meaning: A uniform scaling of target/test covariances scales the incremental explained variance quadratically.
 Exact checked proposition: forall a b c u v k, cov2_innovation_gain a b c (k*u) (k*v)=k*k*cov2_innovation_gain a b c u v.
 Premises and side conditions: Target-covariance scaling is purely algebraic and does not require positive definiteness.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_target_scale :
 forall a b c u v k, cov2_innovation_gain a b c (k*u) (k*v)=k*k*cov2_innovation_gain a b c u v.
Proof.
 intros a b c u v k; unfold cov2_innovation_gain,Rdiv.
 rewrite cov2_innovation_covariance_homogeneous.
 ring.
Qed.

(**
 [cov2_innovation_gain_projection_invariance] (theorem) — Residual predictive information is unchanged when the target cross-covariance vector gains a multiple of the first observed score's covariance column.
 Mathematical meaning: Residual predictive information is unchanged when the target cross-covariance vector gains a multiple of the first observed score's covariance column.
 Exact checked proposition: forall a b c u v k, a<>0 -> cov2_innovation_gain a b c (u+k*a) (v+k*c)=cov2_innovation_gain a b c u v.
 Premises and side conditions: First marginal nonzero; this is an exact partial-regression invariance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_projection_invariance :
 forall a b c u v k, a<>0 -> cov2_innovation_gain a b c (u+k*a) (v+k*c)=cov2_innovation_gain a b c u v.
Proof.
 intros a b c u v k Ha; unfold cov2_innovation_gain.
 rewrite (cov2_innovation_covariance_first_projection_invariance a c u v k Ha).
 reflexivity.
Qed.

(**
 [cov2_innovation_gain_polarization] (theorem) — The gain of a sum of two independent target covariance vectors contains their two gains and their precise cross term.
 Mathematical meaning: The gain of a sum of two independent target covariance vectors contains their two gains and their precise cross term.
 Exact checked proposition: forall a b c u v p q, cov2_innovation_gain a b c (u+p) (v+q) = cov2_innovation_gain a b c u v + cov2_innovation_gain a b c p q + 2*cov2_innovation_covariance a c u v*cov2_innovation_covariance a c p q / cov2_innovation_variance a b c.
 Premises and side conditions: All identities hold under totalized real division; statistical interpretation requires positive innovation variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_polarization :
 forall a b c u v p q, cov2_innovation_gain a b c (u+p) (v+q) = cov2_innovation_gain a b c u v + cov2_innovation_gain a b c p q + 2*cov2_innovation_covariance a c u v*cov2_innovation_covariance a c p q / cov2_innovation_variance a b c.
Proof.
 intros a b c u v p q; unfold cov2_innovation_gain,Rdiv.
 rewrite cov2_innovation_covariance_additive.
 ring.
Qed.

(**
 [cov2_innovation_gain_parallelogram] (theorem) — A parallelogram identity determines information gain under opposite perturbations of the target signal.
 Mathematical meaning: A parallelogram identity determines information gain under opposite perturbations of the target signal.
 Exact checked proposition: forall a b c u v p q, cov2_innovation_gain a b c (u+p) (v+q) + cov2_innovation_gain a b c (u-p) (v-q) = 2*cov2_innovation_gain a b c u v + 2*cov2_innovation_gain a b c p q.
 Premises and side conditions: Purely algebraic quadratic identity requiring no independence assumptions.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_innovation_gain_parallelogram :
 forall a b c u v p q, cov2_innovation_gain a b c (u+p) (v+q) + cov2_innovation_gain a b c (u-p) (v-q) = 2*cov2_innovation_gain a b c u v + 2*cov2_innovation_gain a b c p q.
Proof.
 intros a b c u v p q.
 (* Unfold division last: residualized covariances contain nested quotients. *)
 unfold cov2_innovation_gain,cov2_innovation_covariance,Rdiv.
 ring.
Qed.

(**
 [cov2_schur_incremental_innovation] (theorem) — The exact improvement in best linear residual variance from adding observation two is its innovation gain.
 Mathematical meaning: The exact improvement in best linear residual variance from adding observation two is its innovation gain.
 Exact checked proposition: forall a b c u v s, a<>0 -> cov2_det a b c<>0 -> cov2_one_risk a u s-cov2_schur a b c u v s=cov2_innovation_gain a b c u v.
 Premises and side conditions: First marginal and full observed covariance block are nonsingular.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_incremental_innovation :
 forall a b c u v s, a<>0 -> cov2_det a b c<>0 -> cov2_one_risk a u s-cov2_schur a b c u v s=cov2_innovation_gain a b c u v.
Proof.
 intros a b c u v s Ha Hd.
 rewrite cov2_one_to_two_gain by assumption.
 symmetry; apply cov2_innovation_gain_partial_rational; assumption.
Qed.

(**
 [cov2_schur_no_innovation_iff] (theorem) — The second test fails to reduce optimal residual variance exactly when its partialed-out target signal vanishes.
 Mathematical meaning: The second test fails to reduce optimal residual variance exactly when its partialed-out target signal vanishes.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> (cov2_schur a b c u v s=cov2_one_risk a u s <-> cov2_innovation_covariance a c u v=0).
 Premises and side conditions: Positive covariance minors ensure regression uniqueness and proper residual variances.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_no_innovation_iff :
 forall a b c u v s, 0<a -> 0<cov2_det a b c -> (cov2_schur a b c u v s=cov2_one_risk a u s <-> cov2_innovation_covariance a c u v=0).
Proof.
 intros a b c u v s Ha Hd.
 rewrite (cov2_no_additional_gain_iff a b c u v s Ha Hd).
 symmetry; apply cov2_innovation_covariance_zero_iff; lra.
Qed.

(**
 [cov2_schur_strict_innovation_iff] (theorem) — Adding the second test strictly improves linear prediction exactly when its innovation target covariance is nonzero.
 Mathematical meaning: Adding the second test strictly improves linear prediction exactly when its innovation target covariance is nonzero.
 Exact checked proposition: forall a b c u v s, 0<a -> 0<cov2_det a b c -> (cov2_schur a b c u v s<cov2_one_risk a u s <-> cov2_innovation_covariance a c u v<>0).
 Premises and side conditions: Both covariance minors are positive; no Gaussian conditioning is inferred.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_strict_innovation_iff :
 forall a b c u v s, 0<a -> 0<cov2_det a b c -> (cov2_schur a b c u v s<cov2_one_risk a u s <-> cov2_innovation_covariance a c u v<>0).
Proof.
 intros a b c u v s Ha Hd.
 pose proof (cov2_two_obs_improves_one a b c u v s Ha Hd) as Hweak.
 pose proof (cov2_schur_no_innovation_iff a b c u v s Ha Hd) as Hiff.
 split; intro H.
 - intro Hzero; apply (proj2 Hiff) in Hzero; lra.
 - assert (Hneq:cov2_schur a b c u v s<>cov2_one_risk a u s).
   { intro He; apply H; apply (proj1 Hiff); exact He. }
   lra.
Qed.

(**
 [cov2_quad_innovation_diagonal] (theorem) — The observed covariance quadratic energy diagonalizes into the first-test squared component and an orthogonalized second-test residual energy.
 Mathematical meaning: The observed covariance quadratic energy diagonalizes into the first-test squared component and an orthogonalized second-test residual energy.
 Exact checked proposition: forall a b c x y, a<>0 -> cov2_quad a b c x y = a*(x+c*y/a)*(x+c*y/a)+cov2_innovation_variance a b c*y*y.
 Premises and side conditions: First-test marginal variance must be nonzero.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_quad_innovation_diagonal :
 forall a b c x y, a<>0 -> cov2_quad a b c x y = a*(x+c*y/a)*(x+c*y/a)+cov2_innovation_variance a b c*y*y.
Proof.
 intros a b c x y Ha.
 unfold cov2_quad,cov2_innovation_variance; field; exact Ha.
Qed.

(**
 [cov2_quad_innovation_semidefinite] (theorem) — Nonnegative first variance and innovation variance ensure nonnegative covariance quadratic energy for any linear predictor weights.
 Mathematical meaning: Nonnegative first variance and innovation variance ensure nonnegative covariance quadratic energy for any linear predictor weights.
 Exact checked proposition: forall a b c x y, 0<a -> 0<=cov2_innovation_variance a b c -> 0<=cov2_quad a b c x y.
 Premises and side conditions: First-test variance positive and innovation residual variance nonnegative.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_quad_innovation_semidefinite :
 forall a b c x y, 0<a -> 0<=cov2_innovation_variance a b c -> 0<=cov2_quad a b c x y.
Proof.
 intros a b c x y Ha Hv.
 rewrite (cov2_quad_innovation_diagonal a b c x y ltac:(lra)).
 assert (Hsq:0<=(x+c*y/a)*(x+c*y/a)).
 { change (0<=Rsqr (x+c*y/a)); apply Rle_0_sqr. }
 assert (Hsqy:0<=y*y).
 { change (0<=Rsqr y); apply Rle_0_sqr. }
 assert (Hp:0<=a*((x+c*y/a)*(x+c*y/a))).
 { apply Rmult_le_pos; [lra|exact Hsq]. }
 assert (Hq:0<=cov2_innovation_variance a b c*(y*y)).
 { apply Rmult_le_pos; [exact Hv|exact Hsqy]. }
 lra.
Qed.

(**
 [cov2_beta_first_uncorrelated] (theorem) — With zero inter-test covariance, the first partial regression coefficient is exactly the one-test slope.
 Mathematical meaning: With zero inter-test covariance, the first partial regression coefficient is exactly the one-test slope.
 Exact checked proposition: forall a b u v, a<>0 -> b<>0 -> cov2_beta_first a b 0 u v=u/a.
 Premises and side conditions: Both observed variances must be nonzero.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_first_uncorrelated :
 forall a b u v, a<>0 -> b<>0 -> cov2_beta_first a b 0 u v=u/a.
Proof.
 intros a b u v Ha Hb.
 unfold cov2_beta_first,cov2_det; field; nra.
Qed.

(**
 [cov2_beta_second_uncorrelated] (theorem) — With zero inter-test covariance, the second partial regression coefficient is the univariate slope on test two.
 Mathematical meaning: With zero inter-test covariance, the second partial regression coefficient is the univariate slope on test two.
 Exact checked proposition: forall a b u v, a<>0 -> b<>0 -> cov2_beta_second a b 0 u v=v/b.
 Premises and side conditions: Both observed variances must be nonzero.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_second_uncorrelated :
 forall a b u v, a<>0 -> b<>0 -> cov2_beta_second a b 0 u v=v/b.
Proof.
 intros a b u v Ha Hb.
 unfold cov2_beta_second,cov2_det; field; nra.
Qed.

(**
 [cov2_schur_uncorrelated] (theorem) — For uncorrelated observations the optimal two-test residual is the target variance minus the two independent algebraic explained-variance terms.
 Mathematical meaning: For uncorrelated observations the optimal two-test residual is the target variance minus the two independent algebraic explained-variance terms.
 Exact checked proposition: forall a b u v s, a<>0 -> b<>0 -> cov2_schur a b 0 u v s=s-u*u/a-v*v/b.
 Premises and side conditions: Algebraic uncorrelated observations; not stochastic independence unless a separate Gaussian assumption is proved.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_uncorrelated :
 forall a b u v s, a<>0 -> b<>0 -> cov2_schur a b 0 u v s=s-u*u/a-v*v/b.
Proof.
 intros a b u v s Ha Hb.
 unfold cov2_schur.
 rewrite (cov2_beta_first_uncorrelated a b u v Ha Hb).
 rewrite (cov2_beta_second_uncorrelated a b u v Ha Hb).
 unfold Rdiv; ring.
Qed.

(**
 [cov2_beta_second_projection_invariant] (theorem) — Adding a component explained by the first score to the target covariance leaves the second partial slope unchanged.
 Mathematical meaning: Adding a component explained by the first score to the target covariance leaves the second partial slope unchanged.
 Exact checked proposition: forall a b c u v k, cov2_det a b c<>0 -> cov2_beta_second a b c (u+k*a) (v+k*c)=cov2_beta_second a b c u v.
 Premises and side conditions: The observed covariance determinant must be nonsingular for a statistical regression interpretation.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_second_projection_invariant :
 forall a b c u v k, cov2_det a b c<>0 -> cov2_beta_second a b c (u+k*a) (v+k*c)=cov2_beta_second a b c u v.
Proof.
 intros a b c u v k Hd.
 unfold cov2_beta_second,Rdiv; ring.
Qed.

(**
 [cov2_beta_first_projection_shift] (theorem) — Adding a multiple of the first score to the target covariance increases the first optimal slope by that multiple.
 Mathematical meaning: Adding a multiple of the first score to the target covariance increases the first optimal slope by that multiple.
 Exact checked proposition: forall a b c u v k, cov2_det a b c<>0 -> cov2_beta_first a b c (u+k*a) (v+k*c)=cov2_beta_first a b c u v+k.
 Premises and side conditions: The covariance determinant must be nonzero and observation-one signal shifts are consistent.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_beta_first_projection_shift :
 forall a b c u v k, cov2_det a b c<>0 -> cov2_beta_first a b c (u+k*a) (v+k*c)=cov2_beta_first a b c u v+k.
Proof.
 intros a b c u v k Hd.
 unfold cov2_beta_first,Rdiv.
 replace ((b*(u+k*a)-c*(v+k*c))* /cov2_det a b c)
 with ((b*u-c*v)* /cov2_det a b c+
   k*(cov2_det a b c* /cov2_det a b c))
 by (unfold cov2_det; ring).
 rewrite Rinv_r by exact Hd.
 ring.
Qed.

(**
 [cov2_det_noise_second] (theorem) — Additional second-test variance raises the observed covariance determinant by the first-test variance times the perturbation.
 Mathematical meaning: Additional second-test variance raises the observed covariance determinant by the first-test variance times the perturbation.
 Exact checked proposition: forall a b c t, cov2_det a (b+t) c=cov2_det a b c+a*t.
 Premises and side conditions: Noise is represented algebraically by a nonnegative variance addition when interpreting as independent measurement error.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_det_noise_second :
 forall a b c t, cov2_det a (b+t) c=cov2_det a b c+a*t.
Proof.
 intros; unfold cov2_det; ring.
Qed.

(**
 [cov2_det_noise_first] (theorem) — Additional first-test variance raises the determinant by the second-test variance times the perturbation.
 Mathematical meaning: Additional first-test variance raises the determinant by the second-test variance times the perturbation.
 Exact checked proposition: forall a b c t, cov2_det (a+t) b c=cov2_det a b c+b*t.
 Premises and side conditions: Interpretation as noise requires nonnegative variance shift; equality holds for all real t.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_det_noise_first :
 forall a b c t, cov2_det (a+t) b c=cov2_det a b c+b*t.
Proof.
 intros; unfold cov2_det; ring.
Qed.

(**
 [cov2_det_noise_both] (theorem) — Adding noise to both tests yields the exact mixed determinant increase including the product of both noise variances.
 Mathematical meaning: Adding noise to both tests yields the exact mixed determinant increase including the product of both noise variances.
 Exact checked proposition: forall a b c t w, cov2_det (a+t) (b+w) c=cov2_det a b c+a*w+b*t+t*w.
 Premises and side conditions: Quadratic covariance determinant identity; probabilistic modeling requires independent centered noise.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_det_noise_both :
 forall a b c t w, cov2_det (a+t) (b+w) c=cov2_det a b c+a*w+b*t+t*w.
Proof.
 intros; unfold cov2_det; ring.
Qed.

(**
 [cov2_det_noise_second_positive] (theorem) — A positive-definite observed covariance block remains invertible after adding nonnegative independent noise to its second diagonal.
 Mathematical meaning: A positive-definite observed covariance block remains invertible after adding nonnegative independent noise to its second diagonal.
 Exact checked proposition: forall a b c t, 0<a -> 0<cov2_det a b c -> 0<=t -> 0<cov2_det a (b+t) c.
 Premises and side conditions: Positive first variance, positive determinant, and nonnegative noise are required.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_det_noise_second_positive :
 forall a b c t, 0<a -> 0<cov2_det a b c -> 0<=t -> 0<cov2_det a (b+t) c.
Proof.
 intros a b c t Ha Hd Ht; rewrite cov2_det_noise_second; nra.
Qed.

(**
 [cov2_det_noise_first_positive] (theorem) — A positive-definite observed covariance block stays invertible after adding nonnegative first-test measurement variance.
 Mathematical meaning: A positive-definite observed covariance block stays invertible after adding nonnegative first-test measurement variance.
 Exact checked proposition: forall a b c t, 0<b -> 0<cov2_det a b c -> 0<=t -> 0<cov2_det (a+t) b c.
 Premises and side conditions: Positive second variance and positive determinant with nonnegative first noise.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_det_noise_first_positive :
 forall a b c t, 0<b -> 0<cov2_det a b c -> 0<=t -> 0<cov2_det (a+t) b c.
Proof.
 intros a b c t Hb Hd Ht; rewrite cov2_det_noise_first; nra.
Qed.

(**
 [cov2_det_noise_both_positive] (theorem) — Simultaneous nonnegative diagonal noise inflation preserves strict positivity of the two-by-two covariance determinant.
 Mathematical meaning: Simultaneous nonnegative diagonal noise inflation preserves strict positivity of the two-by-two covariance determinant.
 Exact checked proposition: forall a b c t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> 0<cov2_det (a+t) (b+w) c.
 Premises and side conditions: Original block positive definite with both noise variances nonnegative.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_det_noise_both_positive :
 forall a b c t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> 0<cov2_det (a+t) (b+w) c.
Proof.
 intros a b c t w Ha Hb Hd Ht Hw; rewrite cov2_det_noise_both; nra.
Qed.

(**
 [cov2_risk_noise_second] (theorem) — Independent variance inflation of the second observation raises the risk of any fixed linear predictor by t times its squared second coefficient.
 Mathematical meaning: Independent variance inflation of the second observation raises the risk of any fixed linear predictor by t times its squared second coefficient.
 Exact checked proposition: forall a b c u v s x y t, cov2_risk a (b+t) c u v s x y=cov2_risk a b c u v s x y+t*y*y.
 Premises and side conditions: No positivity is required for the algebraic identity; noise interpretation assumes nonnegative t.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_second :
 forall a b c u v s x y t, cov2_risk a (b+t) c u v s x y=cov2_risk a b c u v s x y+t*y*y.
Proof.
 intros; unfold cov2_risk,cov2_quad; ring.
Qed.

(**
 [cov2_risk_noise_first] (theorem) — Increasing first-test variance raises fixed-coefficient mean-square risk by the noise variance times the first coefficient squared.
 Mathematical meaning: Increasing first-test variance raises fixed-coefficient mean-square risk by the noise variance times the first coefficient squared.
 Exact checked proposition: forall a b c u v s x y t, cov2_risk (a+t) b c u v s x y=cov2_risk a b c u v s x y+t*x*x.
 Premises and side conditions: No positivity assumption for the identity; nonnegative t is needed for physical noise.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_first :
 forall a b c u v s x y t, cov2_risk (a+t) b c u v s x y=cov2_risk a b c u v s x y+t*x*x.
Proof.
 intros; unfold cov2_risk,cov2_quad; ring.
Qed.

(**
 [cov2_risk_noise_both] (theorem) — Simultaneously inflating both test variances adds their two coefficient-weighted noise-risk penalties.
 Mathematical meaning: Simultaneously inflating both test variances adds their two coefficient-weighted noise-risk penalties.
 Exact checked proposition: forall a b c u v s x y t w, cov2_risk (a+t) (b+w) c u v s x y=cov2_risk a b c u v s x y+t*x*x+w*y*y.
 Premises and side conditions: Noise modeled as independent diagonal variance inflation; no Gaussian probability is asserted.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_both :
 forall a b c u v s x y t w, cov2_risk (a+t) (b+w) c u v s x y=cov2_risk a b c u v s x y+t*x*x+w*y*y.
Proof.
 intros; unfold cov2_risk,cov2_quad; ring.
Qed.

(**
 [cov2_risk_noise_second_monotone] (theorem) — A fixed linear predictor cannot improve its risk by increasing nonnegative second-test measurement noise.
 Mathematical meaning: A fixed linear predictor cannot improve its risk by increasing nonnegative second-test measurement noise.
 Exact checked proposition: forall a b c u v s x y t, 0<=t -> cov2_risk a b c u v s x y<=cov2_risk a (b+t) c u v s x y.
 Premises and side conditions: Nonnegative additional second-test variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_second_monotone :
 forall a b c u v s x y t, 0<=t -> cov2_risk a b c u v s x y<=cov2_risk a (b+t) c u v s x y.
Proof.
 intros a b c u v s x y t Ht.
 rewrite cov2_risk_noise_second.
 assert (Hsq:0<=y*y) by (change (0<=Rsqr y); apply Rle_0_sqr).
 assert (Hpen:0<=t*y*y).
 { replace (t*y*y) with (t*(y*y)) by ring.
   apply Rmult_le_pos; assumption. }
 lra.
Qed.

(**
 [cov2_risk_noise_first_monotone] (theorem) — A fixed linear predictor cannot improve risk after nonnegative first-test noise inflation.
 Mathematical meaning: A fixed linear predictor cannot improve risk after nonnegative first-test noise inflation.
 Exact checked proposition: forall a b c u v s x y t, 0<=t -> cov2_risk a b c u v s x y<=cov2_risk (a+t) b c u v s x y.
 Premises and side conditions: Nonnegative additional first-test variance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_first_monotone :
 forall a b c u v s x y t, 0<=t -> cov2_risk a b c u v s x y<=cov2_risk (a+t) b c u v s x y.
Proof.
 intros a b c u v s x y t Ht.
 rewrite cov2_risk_noise_first.
 assert (Hsq:0<=x*x) by (change (0<=Rsqr x); apply Rle_0_sqr).
 assert (Hpen:0<=t*x*x).
 { replace (t*x*x) with (t*(x*x)) by ring.
   apply Rmult_le_pos; assumption. }
 lra.
Qed.

(**
 [cov2_risk_noise_both_monotone] (theorem) — A predictor's fixed-coefficient risk weakly increases under simultaneous nonnegative independent noise inflation.
 Mathematical meaning: A predictor's fixed-coefficient risk weakly increases under simultaneous nonnegative independent noise inflation.
 Exact checked proposition: forall a b c u v s x y t w, 0<=t -> 0<=w -> cov2_risk a b c u v s x y<=cov2_risk (a+t) (b+w) c u v s x y.
 Premises and side conditions: Both variance-inflation parameters are nonnegative.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_both_monotone :
 forall a b c u v s x y t w, 0<=t -> 0<=w -> cov2_risk a b c u v s x y<=cov2_risk (a+t) (b+w) c u v s x y.
Proof.
 intros a b c u v s x y t w Ht Hw.
 rewrite cov2_risk_noise_both.
 assert (Hsqx:0<=x*x) by (change (0<=Rsqr x); apply Rle_0_sqr).
 assert (Hsqy:0<=y*y) by (change (0<=Rsqr y); apply Rle_0_sqr).
 assert (Hpenx:0<=t*x*x).
 { replace (t*x*x) with (t*(x*x)) by ring.
   apply Rmult_le_pos; assumption. }
 assert (Hpeny:0<=w*y*y).
 { replace (w*y*y) with (w*(y*y)) by ring.
   apply Rmult_le_pos; assumption. }
 lra.
Qed.

(**
 [cov2_risk_noise_second_strict] (theorem) — Positive added variance strictly worsens a fixed linear predictor whenever its second weight is nonzero.
 Mathematical meaning: Positive added variance strictly worsens a fixed linear predictor whenever its second weight is nonzero.
 Exact checked proposition: forall a b c u v s x y t, 0<t -> y<>0 -> cov2_risk a b c u v s x y<cov2_risk a (b+t) c u v s x y.
 Premises and side conditions: Positive second-test noise and a nonzero second coefficient.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_second_strict :
 forall a b c u v s x y t, 0<t -> y<>0 -> cov2_risk a b c u v s x y<cov2_risk a (b+t) c u v s x y.
Proof.
 intros a b c u v s x y t Ht Hy.
 rewrite cov2_risk_noise_second.
 assert (Hsq:0<y*y) by nra.
 assert (Hpen:0<t*y*y).
 { replace (t*y*y) with (t*(y*y)) by ring.
   apply Rmult_lt_0_compat; assumption. }
 lra.
Qed.

(**
 [cov2_risk_noise_first_strict] (theorem) — Positive first-test noise strictly worsens a fixed predictor using a nonzero first score coefficient.
 Mathematical meaning: Positive first-test noise strictly worsens a fixed predictor using a nonzero first score coefficient.
 Exact checked proposition: forall a b c u v s x y t, 0<t -> x<>0 -> cov2_risk a b c u v s x y<cov2_risk (a+t) b c u v s x y.
 Premises and side conditions: Positive first-test noise and a nonzero first regression weight.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_risk_noise_first_strict :
 forall a b c u v s x y t, 0<t -> x<>0 -> cov2_risk a b c u v s x y<cov2_risk (a+t) b c u v s x y.
Proof.
 intros a b c u v s x y t Ht Hx.
 rewrite cov2_risk_noise_first.
 assert (Hsq:0<x*x) by nra.
 assert (Hpen:0<t*x*x).
 { replace (t*x*x) with (t*(x*x)) by ring.
   apply Rmult_lt_0_compat; assumption. }
 lra.
Qed.

(**
 [cov2_schur_noise_second_monotone] (theorem) — Even after optimal reweighting, extra noise on the second test cannot reduce the minimum achievable linear prediction risk.
 Mathematical meaning: Even after optimal reweighting, extra noise on the second test cannot reduce the minimum achievable linear prediction risk.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur a (b+t) c u v s.
 Premises and side conditions: Positive-definite original observed covariance, nonnegative added second-test noise.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_second_monotone :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur a (b+t) c u v s.
Proof.
 intros a b c u v s t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c).
 { apply cov2_det_noise_second_positive; assumption. }
 set (p:=cov2_beta_first a (b+t) c u v).
 set (q:=cov2_beta_second a (b+t) c u v).
 pose proof (cov2_risk_minimizer a b c u v s p q Ha Hd) as Hmin.
 pose proof (cov2_risk_noise_second_monotone a b c u v s p q t Ht) as Hnoise.
 pose proof (cov2_risk_at_optimum a (b+t) c u v s ltac:(lra)) as Hopt.
 change (cov2_risk a (b+t) c u v s p q=cov2_schur a (b+t) c u v s) in Hopt.
 lra.
Qed.

(**
 [cov2_schur_noise_first_monotone] (theorem) — Even after optimal reweighting, extra noise on the first test cannot reduce the minimum achievable linear prediction risk.
 Mathematical meaning: Even after optimal reweighting, extra noise on the first test cannot reduce the minimum achievable linear prediction risk.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur (a+t) b c u v s.
 Premises and side conditions: Positive second observed variance, original positive determinant, and nonnegative first noise.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_first_monotone :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur (a+t) b c u v s.
Proof.
 intros a b c u v s t Hb Hd Ht.
 rewrite (cov2_schur_swap a b c u v s).
 rewrite (cov2_schur_swap (a+t) b c u v s).
 apply (cov2_schur_noise_second_monotone b a c v u s t); try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_both_monotone] (theorem) — Optimal risk is monotone in simultaneous independent noise variances for both observed tests.
 Mathematical meaning: Optimal risk is monotone in simultaneous independent noise variances for both observed tests.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur a b c u v s<=cov2_schur (a+t) (b+w) c u v s.
 Premises and side conditions: Positive original principal minors and determinant, and nonnegative diagonal noise additions.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_both_monotone :
 forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur a b c u v s<=cov2_schur (a+t) (b+w) c u v s.
Proof.
 intros a b c u v s t w Ha Hb Hd Ht Hw.
 assert (Hd1:0<cov2_det (a+t) b c)
   by (apply cov2_det_noise_first_positive; assumption).
 pose proof (cov2_schur_noise_first_monotone a b c u v s t Hb Hd Ht) as H1.
 pose proof (cov2_schur_noise_second_monotone (a+t) b c u v s w ltac:(lra) Hd1 Hw) as H2.
 lra.
Qed.

(**
 [cov2_schur_noise_second_upper_one_test] (theorem) — Even under arbitrarily large nonnegative second-test noise, optimal two-test risk never exceeds the original first-test-only risk.
 Mathematical meaning: Even under arbitrarily large nonnegative second-test noise, optimal two-test risk never exceeds the original first-test-only risk.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a (b+t) c u v s<=cov2_one_risk a u s.
 Premises and side conditions: Positive-definite covariance plus nonnegative additional noise.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_second_upper_one_test :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a (b+t) c u v s<=cov2_one_risk a u s.
Proof.
 intros a b c u v s t Ha Hd Ht.
 apply cov2_two_obs_improves_one; [exact Ha|].
 apply cov2_det_noise_second_positive; assumption.
Qed.

(**
 [cov2_schur_noise_second_sandwich] (theorem) — The optimal linear residual risk with second-test noise lies between its noiseless two-test optimum and the first-test-only optimum.
 Mathematical meaning: The optimal linear residual risk with second-test noise lies between its noiseless two-test optimum and the first-test-only optimum.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur a (b+t) c u v s /\ cov2_schur a (b+t) c u v s<=cov2_one_risk a u s.
 Premises and side conditions: Second-score measurement-noise variance is nonnegative.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_second_sandwich :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur a (b+t) c u v s /\ cov2_schur a (b+t) c u v s<=cov2_one_risk a u s.
Proof.
 intros a b c u v s t Ha Hd Ht.
 split; [apply cov2_schur_noise_second_monotone|apply cov2_schur_noise_second_upper_one_test]; assumption.
Qed.

(**
 [cov2_schur_noise_second_bound_by_old_slope] (theorem) — The increase in optimal risk from second-score noise is bounded above by noise variance times the squared noiseless optimal second coefficient.
 Mathematical meaning: The increase in optimal risk from second-score noise is bounded above by noise variance times the squared noiseless optimal second coefficient.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a (b+t) c u v s <= cov2_schur a b c u v s + t*cov2_beta_second a b c u v*cov2_beta_second a b c u v.
 Premises and side conditions: Original observed covariance positive definite and added second-test noise nonnegative.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_second_bound_by_old_slope :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a (b+t) c u v s <= cov2_schur a b c u v s + t*cov2_beta_second a b c u v*cov2_beta_second a b c u v.
Proof.
 intros a b c u v s t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 set (p:=cov2_beta_first a b c u v).
 set (q:=cov2_beta_second a b c u v).
 pose proof (cov2_risk_minimizer a (b+t) c u v s p q Ha Hdnew) as Hmin.
 pose proof (cov2_risk_at_optimum a b c u v s ltac:(lra)) as Hold.
 pose proof (cov2_risk_noise_second a b c u v s p q t) as Hnoise.
 change (cov2_risk a b c u v s p q=cov2_schur a b c u v s) in Hold.
 lra.
Qed.

(**
 [cov2_schur_noise_second_zero_partial] (theorem) — If the second test has no residual target signal, adding nonnegative noise to that test leaves optimal residual risk unchanged.
 Mathematical meaning: If the second test has no residual target signal, adding nonnegative noise to that test leaves optimal residual risk unchanged.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> a*v=c*u -> cov2_schur a (b+t) c u v s=cov2_schur a b c u v s.
 Premises and side conditions: Strict positive definiteness and exact zero partial target covariance.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_second_zero_partial :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> a*v=c*u -> cov2_schur a (b+t) c u v s=cov2_schur a b c u v s.
Proof.
 intros a b c u v s t Ha Hd Ht Hzero.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 pose proof (proj2 (cov2_no_additional_gain_iff a b c u v s Ha Hd) Hzero) as H1.
 pose proof (proj2 (cov2_no_additional_gain_iff a (b+t) c u v s Ha Hdnew) Hzero) as H2.
 lra.
Qed.

(**
 [cov2_schur_noise_second_nonnegative] (theorem) — If the original best two-test residual variance is nonnegative, adding independent second-test noise preserves that nonnegativity.
 Mathematical meaning: If the original best two-test residual variance is nonnegative, adding independent second-test noise preserves that nonnegativity.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> 0<=cov2_schur a b c u v s -> 0<=cov2_schur a (b+t) c u v s.
 Premises and side conditions: Requires an initially nonnegative optimal residual variance plus nonnegative added noise.
 Proof/definition method: Reuse the existing checked Schur normal-equation, determinant, optimal-risk and strict-gain results. Reduce new identities using Stdlib real ring/field arithmetic and strict-positive covariance lemmas; preserve every side condition explicitly.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, sqrt where applicable, and the already-kernel-checked TwoObservationSchur.v results; no duplicated matrix inversion, no new axioms, and no unverified numerical solver.
 Boundary: Statements concern exact real covariance matrices and best linear predictors only. No Gaussian existence, continuous conditional distribution, normal tail, stochastic independence of additive errors, or empirical IQ calibration is proved.
 *)
Theorem cov2_schur_noise_second_nonnegative :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> 0<=cov2_schur a b c u v s -> 0<=cov2_schur a (b+t) c u v s.
Proof.
 intros a b c u v s t Ha Hd Ht Hschur.
 pose proof (cov2_schur_noise_second_monotone a b c u v s t Ha Hd Ht).
 lra.
Qed.


(* D030x — strict noise sensitivity and exact innovation/equality cases for
   sequential best-linear prediction, formalized with existing Schur lemmas. *)

(**
 [cov2_pd_second_variance_positive] (theorem) — Positive definiteness of the two-test covariance block forces positive variance for its second score.
 Mathematical meaning: Positive definiteness of the two-test covariance block forces positive variance for its second score.
 Exact checked proposition: forall a b c, 0<a -> 0<cov2_det a b c -> 0<b.
 Premises and side conditions: Assumes a positive first diagonal and strictly positive covariance determinant.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_pd_second_variance_positive :
 forall a b c, 0<a -> 0<cov2_det a b c -> 0<b.
Proof.
 intros a b c Ha Hd.
 unfold cov2_det in Hd.
 assert (Hsq:0<=c*c) by nra.
 nra.
Qed.

(**
 [cov2_pd_strict_cross_covariance_bound] (theorem) — Positive determinant yields the strict two-score Cauchy covariance inequality.
 Mathematical meaning: Positive determinant yields the strict two-score Cauchy covariance inequality.
 Exact checked proposition: forall a b c, 0<cov2_det a b c -> c*c<a*b.
 Premises and side conditions: Uses strictly positive covariance determinant.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_pd_strict_cross_covariance_bound :
 forall a b c, 0<cov2_det a b c -> c*c<a*b.
Proof.
 intros a b c Hd; unfold cov2_det in Hd; lra.
Qed.

(**
 [cov2_innovation_variance_upper_second] (theorem) — Residualizing the second score against the first never increases its variance.
 Mathematical meaning: Residualizing the second score against the first never increases its variance.
 Exact checked proposition: forall a b c, 0<a -> cov2_innovation_variance a b c<=b.
 Premises and side conditions: Positive first-test variance is essential for the inequality.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_variance_upper_second :
 forall a b c, 0<a -> cov2_innovation_variance a b c<=b.
Proof.
 intros a b c Ha.
 unfold cov2_innovation_variance,Rdiv.
 assert (Hi:0<=/a) by (apply Rlt_le,Rinv_0_lt_compat; exact Ha).
 assert (Hs:0<=c*c) by nra.
 assert (Hp:0<=c*c* /a) by (apply Rmult_le_pos; assumption).
 lra.
Qed.

(**
 [cov2_innovation_variance_strict_under_covariance] (theorem) — Residual variance is strictly smaller exactly when the two observed test scores have nonzero covariance.
 Mathematical meaning: Residual variance is strictly smaller exactly when the two observed test scores have nonzero covariance.
 Exact checked proposition: forall a b c, 0<a -> (cov2_innovation_variance a b c<b <-> c<>0).
 Premises and side conditions: Assumes positive first-score variance and does not infer statistical independence.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_variance_strict_under_covariance :
 forall a b c, 0<a -> (cov2_innovation_variance a b c<b <-> c<>0).
Proof.
 intros a b c Ha.
 unfold cov2_innovation_variance,Rdiv.
 assert (Hi:0< /a) by (apply Rinv_0_lt_compat; exact Ha).
 split.
 - intro H; intro Hz; subst c; lra.
 - intro Hc.
   assert (Hs:0<c*c) by nra.
   assert (Hp:0<c*c* /a) by (apply Rmult_lt_0_compat; assumption).
   lra.
Qed.

(**
 [cov2_innovation_variance_uncorrelated] (theorem) — An uncorrelated second test retains all its original variance after residualization.
 Mathematical meaning: An uncorrelated second test retains all its original variance after residualization.
 Exact checked proposition: forall a b, cov2_innovation_variance a b 0=b.
 Premises and side conditions: An identity under totalized real division; statistical conditioning presumes positive variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_variance_uncorrelated :
 forall a b, cov2_innovation_variance a b 0=b.
Proof.
 intros a b; unfold cov2_innovation_variance,Rdiv; ring.
Qed.

(**
 [cov2_innovation_covariance_uncorrelated] (theorem) — Zero inter-test covariance leaves the second target/test covariance unchanged under residualization.
 Mathematical meaning: Zero inter-test covariance leaves the second target/test covariance unchanged under residualization.
 Exact checked proposition: forall a u v, cov2_innovation_covariance a 0 u v=v.
 Premises and side conditions: Algebraic identity for the two-score partial-covariance formula.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_covariance_uncorrelated :
 forall a u v, cov2_innovation_covariance a 0 u v=v.
Proof.
 intros a u v; unfold cov2_innovation_covariance,Rdiv; ring.
Qed.

(**
 [cov2_innovation_pd_equivalence] (theorem) — At positive first variance, positive second innovation variance is equivalent to positive definiteness of the observed block.
 Mathematical meaning: At positive first variance, positive second innovation variance is equivalent to positive definiteness of the observed block.
 Exact checked proposition: forall a b c, 0<a -> (0<cov2_innovation_variance a b c <-> 0<cov2_det a b c).
 Premises and side conditions: Strictly positive first principal minor.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_pd_equivalence :
 forall a b c, 0<a -> (0<cov2_innovation_variance a b c <-> 0<cov2_det a b c).
Proof.
 intros a b c Ha.
 pose proof (cov2_innovation_variance_times_first a b c ltac:(lra)) as He.
 split; intro H; nra.
Qed.

(**
 [cov2_innovation_psd_quadratic_equivalence] (theorem) — The nonnegative residual innovation variance characterizes positive semidefiniteness of the two-score quadratic form.
 Mathematical meaning: The nonnegative residual innovation variance characterizes positive semidefiniteness of the two-score quadratic form.
 Exact checked proposition: forall a b c, 0<a -> ((forall x y, 0<=cov2_quad a b c x y) <-> 0<=cov2_innovation_variance a b c).
 Premises and side conditions: First score variance strictly positive; semidefinite quadratic form quantified over every weight pair.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_psd_quadratic_equivalence :
 forall a b c, 0<a -> ((forall x y, 0<=cov2_quad a b c x y) <-> 0<=cov2_innovation_variance a b c).
Proof.
 intros a b c Ha; split.
 - intro Hq; apply cov2_innovation_variance_nonnegative; [exact Ha|].
   apply (cov2_psd_forces_cauchy a b c Ha Hq).
 - intro Hv; intros x y.
   apply cov2_quad_innovation_semidefinite; assumption.
Qed.

(**
 [cov2_det_noise_second_order] (theorem) — The covariance determinant is nondecreasing in the second score's diagonal noise variance.
 Mathematical meaning: The covariance determinant is nondecreasing in the second score's diagonal noise variance.
 Exact checked proposition: forall a b c t w, 0<=a -> t<=w -> cov2_det a (b+t) c<=cov2_det a (b+w) c.
 Premises and side conditions: First score variance nonnegative; noise levels ordered.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_det_noise_second_order :
 forall a b c t w, 0<=a -> t<=w -> cov2_det a (b+t) c<=cov2_det a (b+w) c.
Proof.
 intros a b c t w Ha Htw.
 rewrite !cov2_det_noise_second; nra.
Qed.

(**
 [cov2_det_noise_second_strict_order] (theorem) — The observed covariance determinant grows strictly when second-test noise grows with positive first variance.
 Mathematical meaning: The observed covariance determinant grows strictly when second-test noise grows with positive first variance.
 Exact checked proposition: forall a b c t w, 0<a -> t<w -> cov2_det a (b+t) c<cov2_det a (b+w) c.
 Premises and side conditions: Positive first score variance and strictly ordered noise levels.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_det_noise_second_strict_order :
 forall a b c t w, 0<a -> t<w -> cov2_det a (b+t) c<cov2_det a (b+w) c.
Proof.
 intros a b c t w Ha Htw.
 rewrite !cov2_det_noise_second; nra.
Qed.

(**
 [cov2_det_noise_first_order] (theorem) — The covariance determinant is nondecreasing in the first score's added diagonal variance.
 Mathematical meaning: The covariance determinant is nondecreasing in the first score's added diagonal variance.
 Exact checked proposition: forall a b c t w, 0<=b -> t<=w -> cov2_det (a+t) b c<=cov2_det (a+w) b c.
 Premises and side conditions: Second score variance nonnegative.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_det_noise_first_order :
 forall a b c t w, 0<=b -> t<=w -> cov2_det (a+t) b c<=cov2_det (a+w) b c.
Proof.
 intros a b c t w Hb Htw.
 rewrite !cov2_det_noise_first; nra.
Qed.

(**
 [cov2_det_noise_first_strict_order] (theorem) — The determinant grows strictly as noise is increased on the first score.
 Mathematical meaning: The determinant grows strictly as noise is increased on the first score.
 Exact checked proposition: forall a b c t w, 0<b -> t<w -> cov2_det (a+t) b c<cov2_det (a+w) b c.
 Premises and side conditions: Strict positivity of the second score variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_det_noise_first_strict_order :
 forall a b c t w, 0<b -> t<w -> cov2_det (a+t) b c<cov2_det (a+w) b c.
Proof.
 intros a b c t w Hb Htw.
 rewrite !cov2_det_noise_first; nra.
Qed.

(**
 [cov2_innovation_variance_noise_order] (theorem) — Innovation variance increases monotonically between arbitrary ordered second-test noise levels.
 Mathematical meaning: Innovation variance increases monotonically between arbitrary ordered second-test noise levels.
 Exact checked proposition: forall a b c t w, t<=w -> cov2_innovation_variance a (b+t) c<=cov2_innovation_variance a (b+w) c.
 Premises and side conditions: An exact variance-shift identity; no separate covariance distribution assumed.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_variance_noise_order :
 forall a b c t w, t<=w -> cov2_innovation_variance a (b+t) c<=cov2_innovation_variance a (b+w) c.
Proof.
 intros a b c t w Htw.
 rewrite !cov2_innovation_variance_noise_shift; lra.
Qed.

(**
 [cov2_innovation_variance_noise_strict_order] (theorem) — Innovation variance grows strictly when the noise variance on the second score increases.
 Mathematical meaning: Innovation variance grows strictly when the noise variance on the second score increases.
 Exact checked proposition: forall a b c t w, t<w -> cov2_innovation_variance a (b+t) c<cov2_innovation_variance a (b+w) c.
 Premises and side conditions: Strict inequality between second-score noise variances.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_variance_noise_strict_order :
 forall a b c t w, t<w -> cov2_innovation_variance a (b+t) c<cov2_innovation_variance a (b+w) c.
Proof.
 intros a b c t w Htw.
 rewrite !cov2_innovation_variance_noise_shift; lra.
Qed.

(**
 [cov2_schur_noise_second_strict_if_partial] (theorem) — Adding positive second-test measurement noise strictly worsens optimal prediction exactly when that test supplies residual target signal.
 Mathematical meaning: Adding positive second-test measurement noise strictly worsens optimal prediction exactly when that test supplies residual target signal.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<t -> a*v<>c*u -> cov2_schur a b c u v s<cov2_schur a (b+t) c u v s.
 Premises and side conditions: Requires positive original covariance minors, positive noise, and nonzero second partial-covariance numerator.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_second_strict_if_partial :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<t -> a*v<>c*u -> cov2_schur a b c u v s<cov2_schur a (b+t) c u v s.
Proof.
 intros a b c u v s t Ha Hd Ht Hpartial.
 assert (Hdnew:0<cov2_det a (b+t) c).
 { apply cov2_det_noise_second_positive; try assumption; lra. }
 assert (Hinnov:cov2_innovation_covariance a c u v<>0).
 { intro H; apply (proj1 (cov2_innovation_covariance_zero_iff a c u v ltac:(lra))) in H; contradiction. }
 assert (Hnewweight:cov2_beta_second a (b+t) c u v<>0).
 { intro H; apply (proj1 (cov2_beta_second_zero_iff_innovation
       a (b+t) c u v Ha Hdnew)) in H; contradiction. }
 set (p:=cov2_beta_first a (b+t) c u v).
 set (q:=cov2_beta_second a (b+t) c u v).
 pose proof (cov2_risk_minimizer a b c u v s p q Ha Hd) as Hminimum.
 pose proof (cov2_risk_noise_second_strict a b c u v s p q t Ht Hnewweight) as Hnoise.
 pose proof (cov2_risk_at_optimum a (b+t) c u v s ltac:(lra)) as Hnew.
 change (cov2_risk a (b+t) c u v s p q=cov2_schur a (b+t) c u v s) in Hnew.
 lra.
Qed.

(**
 [cov2_schur_noise_first_strict_if_partial] (theorem) — The first score's optimal prediction information is strictly degraded by positive additional first-test noise when its partial target covariance is nonzero.
 Mathematical meaning: The first score's optimal prediction information is strictly degraded by positive additional first-test noise when its partial target covariance is nonzero.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<t -> b*u<>c*v -> cov2_schur a b c u v s<cov2_schur (a+t) b c u v s.
 Premises and side conditions: Positive second observed variance, positive determinant, positive first noise and nonzero reverse partial signal.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_strict_if_partial :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<t -> b*u<>c*v -> cov2_schur a b c u v s<cov2_schur (a+t) b c u v s.
Proof.
 intros a b c u v s t Hb Hd Ht Hpartial.
 rewrite (cov2_schur_swap a b c u v s).
 rewrite (cov2_schur_swap (a+t) b c u v s).
 apply cov2_schur_noise_second_strict_if_partial; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_second_eq_iff] (theorem) — Optimal risk is unchanged under second-score noise exactly for zero added variance or a zero partial covariance.
 Mathematical meaning: Optimal risk is unchanged under second-score noise exactly for zero added variance or a zero partial covariance.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_schur a (b+t) c u v s=cov2_schur a b c u v s <-> t=0 \/ a*v=c*u).
 Premises and side conditions: Nonnegative noise and positive-definite original score covariance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_second_eq_iff :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_schur a (b+t) c u v s=cov2_schur a b c u v s <-> t=0 \/ a*v=c*u).
Proof.
 intros a b c u v s t Ha Hd Ht; split.
 - intro H.
   destruct (Req_EM_T t 0) as [H0|H0].
   + left; exact H0.
   + right.
     destruct (Req_EM_T (a*v) (c*u)) as [Hpartial|Hnon].
     * exact Hpartial.
     * exfalso.
       pose proof (cov2_schur_noise_second_strict_if_partial
                     a b c u v s t Ha Hd ltac:(lra) Hnon) as Hstrict.
       lra.
 - intros [H0|Hpartial].
   + subst t; replace (b+0) with b by ring; reflexivity.
   + apply cov2_schur_noise_second_zero_partial; assumption.
Qed.

(**
 [cov2_schur_noise_first_eq_iff] (theorem) — Exact equality cases for first-score measurement-noise sensitivity.
 Mathematical meaning: Exact equality cases for first-score measurement-noise sensitivity.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> (cov2_schur (a+t) b c u v s=cov2_schur a b c u v s <-> t=0 \/ b*u=c*v).
 Premises and side conditions: Original positive-definite covariance and nonnegative added variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_eq_iff :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> (cov2_schur (a+t) b c u v s=cov2_schur a b c u v s <-> t=0 \/ b*u=c*v).
Proof.
 intros a b c u v s t Hb Hd Ht.
 rewrite (cov2_schur_swap (a+t) b c u v s).
 rewrite (cov2_schur_swap a b c u v s).
 apply cov2_schur_noise_second_eq_iff; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_second_strict_iff] (theorem) — A necessary-and-sufficient criterion for strictly increased optimal error under second-test noise.
 Mathematical meaning: A necessary-and-sufficient criterion for strictly increased optimal error under second-test noise.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_schur a b c u v s<cov2_schur a (b+t) c u v s <-> 0<t /\ a*v<>c*u).
 Premises and side conditions: Nonnegative second noise; positive covariance minors; strictness requires both positive noise and residual target signal.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_second_strict_iff :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_schur a b c u v s<cov2_schur a (b+t) c u v s <-> 0<t /\ a*v<>c*u).
Proof.
 intros a b c u v s t Ha Hd Ht; split.
 - intro Hstrict; split.
   + destruct (Req_EM_T t 0) as [H0|Hnon].
     * subst t; replace (b+0) with b in Hstrict by ring; lra.
     * lra.
   + intro Hpartial.
     pose proof (cov2_schur_noise_second_zero_partial
                    a b c u v s t Ha Hd Ht Hpartial) as He.
     lra.
 - intros [Htpos Hpartial].
   apply cov2_schur_noise_second_strict_if_partial; assumption.
Qed.

(**
 [cov2_schur_noise_first_strict_iff] (theorem) — Strictness of noise-induced prediction loss on the first test is characterized by its nonzero partial signal.
 Mathematical meaning: Strictness of noise-induced prediction loss on the first test is characterized by its nonzero partial signal.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> (cov2_schur a b c u v s<cov2_schur (a+t) b c u v s <-> 0<t /\ b*u<>c*v).
 Premises and side conditions: Positive second principal minor, positive determinant and nonnegative first-score noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_strict_iff :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> (cov2_schur a b c u v s<cov2_schur (a+t) b c u v s <-> 0<t /\ b*u<>c*v).
Proof.
 intros a b c u v s t Hb Hd Ht.
 rewrite (cov2_schur_swap a b c u v s).
 rewrite (cov2_schur_swap (a+t) b c u v s).
 apply cov2_schur_noise_second_strict_iff; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_innovation_gain_second_noise_monotone] (theorem) — Incremental explained variance provided by the second score cannot increase when its measurement noise grows.
 Mathematical meaning: Incremental explained variance provided by the second score cannot increase when its measurement noise grows.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_innovation_gain a (b+t) c u v<=cov2_innovation_gain a b c u v.
 Premises and side conditions: Positive-definite score covariance and nonnegative second diagonal noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_gain_second_noise_monotone :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_innovation_gain a (b+t) c u v<=cov2_innovation_gain a b c u v.
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 pose proof (cov2_schur_noise_second_monotone a b c u v 0 t Ha Hd Ht) as Hmono.
 pose proof (cov2_schur_incremental_innovation a b c u v 0 ltac:(lra) ltac:(lra)) as Hold.
 pose proof (cov2_schur_incremental_innovation a (b+t) c u v 0 ltac:(lra) ltac:(lra)) as Hnew.
 lra.
Qed.

(**
 [cov2_innovation_gain_second_noise_strict] (theorem) — Positive added variance strictly decreases second-score incremental explained variance whenever the score contains nonredundant target information.
 Mathematical meaning: Positive added variance strictly decreases second-score incremental explained variance whenever the score contains nonredundant target information.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<t -> a*v<>c*u -> cov2_innovation_gain a (b+t) c u v<cov2_innovation_gain a b c u v.
 Premises and side conditions: Positive noise and nonzero partial covariance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_gain_second_noise_strict :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<t -> a*v<>c*u -> cov2_innovation_gain a (b+t) c u v<cov2_innovation_gain a b c u v.
Proof.
 intros a b c u v t Ha Hd Ht Hpartial.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; try assumption; lra).
 pose proof (cov2_schur_noise_second_strict_if_partial a b c u v 0 t Ha Hd Ht Hpartial) as Hstrict.
 pose proof (cov2_schur_incremental_innovation a b c u v 0 ltac:(lra) ltac:(lra)) as Hold.
 pose proof (cov2_schur_incremental_innovation a (b+t) c u v 0 ltac:(lra) ltac:(lra)) as Hnew.
 lra.
Qed.

(**
 [cov2_innovation_gain_second_noise_eq_iff] (theorem) — Sharp equality characterization for loss of the second test's incremental explained variance.
 Mathematical meaning: Sharp equality characterization for loss of the second test's incremental explained variance.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_innovation_gain a (b+t) c u v=cov2_innovation_gain a b c u v <-> t=0 \/ a*v=c*u).
 Premises and side conditions: Positive covariance minors and nonnegative noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_gain_second_noise_eq_iff :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_innovation_gain a (b+t) c u v=cov2_innovation_gain a b c u v <-> t=0 \/ a*v=c*u).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 pose proof (cov2_schur_incremental_innovation a b c u v 0 ltac:(lra) ltac:(lra)) as Hold.
 pose proof (cov2_schur_incremental_innovation a (b+t) c u v 0 ltac:(lra) ltac:(lra)) as Hnew.
 pose proof (cov2_schur_noise_second_eq_iff a b c u v 0 t Ha Hd Ht) as Hiff.
 split; intro H.
 - apply (proj1 Hiff); lra.
 - apply (proj2 Hiff) in H; lra.
Qed.

(**
 [cov2_innovation_gain_second_noise_strict_iff] (theorem) — Strict loss of incremental information is equivalent to positive measurement noise and a nonzero partial signal.
 Mathematical meaning: Strict loss of incremental information is equivalent to positive measurement noise and a nonzero partial signal.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_innovation_gain a (b+t) c u v<cov2_innovation_gain a b c u v <-> 0<t /\ a*v<>c*u).
 Premises and side conditions: Requires the same nondegenerate score-covariance assumptions as the regression noise model.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_gain_second_noise_strict_iff :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_innovation_gain a (b+t) c u v<cov2_innovation_gain a b c u v <-> 0<t /\ a*v<>c*u).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 pose proof (cov2_schur_incremental_innovation a b c u v 0 ltac:(lra) ltac:(lra)) as Hold.
 pose proof (cov2_schur_incremental_innovation a (b+t) c u v 0 ltac:(lra) ltac:(lra)) as Hnew.
 pose proof (cov2_schur_noise_second_strict_iff a b c u v 0 t Ha Hd Ht) as Hiff.
 split; intro H.
 - apply (proj1 Hiff); lra.
 - apply (proj2 Hiff) in H; lra.
Qed.

(**
 [cov2_innovation_gain_noise_interval] (theorem) — Both the nonnegative value and upper limit of incremental prediction information are robust under second-score noise.
 Mathematical meaning: Both the nonnegative value and upper limit of incremental prediction information are robust under second-score noise.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> 0<=cov2_innovation_gain a (b+t) c u v /\ cov2_innovation_gain a (b+t) c u v<=cov2_innovation_gain a b c u v.
 Premises and side conditions: Positive definite original covariance and nonnegative added second variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_gain_noise_interval :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> 0<=cov2_innovation_gain a (b+t) c u v /\ cov2_innovation_gain a (b+t) c u v<=cov2_innovation_gain a b c u v.
Proof.
 intros a b c u v t Ha Hd Ht; split.
 - apply cov2_innovation_gain_nonnegative; [exact Ha|].
   apply cov2_det_noise_second_positive; assumption.
 - apply cov2_innovation_gain_second_noise_monotone; assumption.
Qed.

(**
 [cov2_innovation_gain_noise_zero_iff] (theorem) — The second test remains completely redundant under any finite nonnegative independent diagonal noise exactly when its partial target signal was already zero.
 Mathematical meaning: The second test remains completely redundant under any finite nonnegative independent diagonal noise exactly when its partial target signal was already zero.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_innovation_gain a (b+t) c u v=0 <-> a*v=c*u).
 Premises and side conditions: Positive-definite covariance and nonnegative noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_gain_noise_zero_iff :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_innovation_gain a (b+t) c u v=0 <-> a*v=c*u).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 rewrite (cov2_innovation_gain_zero_iff a (b+t) c u v Ha Hdnew).
 apply cov2_innovation_covariance_zero_iff; lra.
Qed.

(**
 [cov2_innovation_gain_noise_positive_iff] (theorem) — Finite independent variance inflation cannot completely destroy a nonzero partial target signal.
 Mathematical meaning: Finite independent variance inflation cannot completely destroy a nonzero partial target signal.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (0<cov2_innovation_gain a (b+t) c u v <-> a*v<>c*u).
 Premises and side conditions: Nondegenerate covariance block and finite nonnegative noise variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_innovation_gain_noise_positive_iff :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (0<cov2_innovation_gain a (b+t) c u v <-> a*v<>c*u).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 rewrite (cov2_innovation_gain_positive_iff a (b+t) c u v Ha Hdnew).
 split.
 - intro H; intro He.
   apply H.
   apply (proj2 (cov2_innovation_covariance_zero_iff a c u v ltac:(lra))); exact He.
 - intro H; intro He.
   apply H.
   apply (proj1 (cov2_innovation_covariance_zero_iff a c u v ltac:(lra))); exact He.
Qed.

(**
 [cov2_beta_second_times_innovation_variance] (theorem) — The second optimal regression weight multiplied by its innovation variance equals the partial target covariance.
 Mathematical meaning: The second optimal regression weight multiplied by its innovation variance equals the partial target covariance.
 Exact checked proposition: forall a b c u v, 0<a -> 0<cov2_det a b c -> cov2_beta_second a b c u v * cov2_innovation_variance a b c = cov2_innovation_covariance a c u v.
 Premises and side conditions: Positive-definite observed covariance ensures the residual variance is invertible.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_second_times_innovation_variance :
 forall a b c u v, 0<a -> 0<cov2_det a b c -> cov2_beta_second a b c u v * cov2_innovation_variance a b c = cov2_innovation_covariance a c u v.
Proof.
 intros a b c u v Ha Hd.
 rewrite (cov2_beta_second_from_innovation a b c u v ltac:(lra) ltac:(lra)).
 assert (Hvar:cov2_innovation_variance a b c<>0)
   by (pose proof (cov2_innovation_variance_positive a b c Ha Hd); lra).
 unfold Rdiv; field; exact Hvar.
Qed.

(**
 [cov2_beta_second_noise_conserved_numerator] (theorem) — Noise changes the innovation variance and slope reciprocally while preserving their target partial-covariance product.
 Mathematical meaning: Noise changes the innovation variance and slope reciprocally while preserving their target partial-covariance product.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_beta_second a (b+t) c u v * cov2_innovation_variance a (b+t) c = cov2_beta_second a b c u v * cov2_innovation_variance a b c.
 Premises and side conditions: Positive-definite score block and nonnegative added second variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_second_noise_conserved_numerator :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_beta_second a (b+t) c u v * cov2_innovation_variance a (b+t) c = cov2_beta_second a b c u v * cov2_innovation_variance a b c.
Proof.
 intros a b c u v t Ha Hd Ht.
 rewrite (cov2_beta_second_times_innovation_variance a (b+t) c u v Ha).
 - symmetry; apply cov2_beta_second_times_innovation_variance; assumption.
 - apply cov2_det_noise_second_positive; assumption.
Qed.

(**
 [cov2_beta_second_noise_zero_iff] (theorem) — Under any nonnegative second noise, the second regression weight is exactly zero if and only if the underlying partial target signal vanishes.
 Mathematical meaning: Under any nonnegative second noise, the second regression weight is exactly zero if and only if the underlying partial target signal vanishes.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_beta_second a (b+t) c u v=0 <-> a*v=c*u).
 Premises and side conditions: Positive definite observed covariance and added diagonal variance nonnegative.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_second_noise_zero_iff :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_beta_second a (b+t) c u v=0 <-> a*v=c*u).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 rewrite (cov2_beta_second_zero_iff_innovation a (b+t) c u v Ha Hdnew).
 apply cov2_innovation_covariance_zero_iff; lra.
Qed.

(**
 [cov2_beta_second_noise_zero_preserved] (theorem) — Diagonal noise cannot change whether the second regression coefficient vanishes.
 Mathematical meaning: Diagonal noise cannot change whether the second regression coefficient vanishes.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_beta_second a (b+t) c u v=0 <-> cov2_beta_second a b c u v=0).
 Premises and side conditions: Strictly positive original covariance minors and nonnegative noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_second_noise_zero_preserved :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_beta_second a (b+t) c u v=0 <-> cov2_beta_second a b c u v=0).
Proof.
 intros a b c u v t Ha Hd Ht.
 rewrite (cov2_beta_second_noise_zero_iff a b c u v t Ha Hd Ht).
 rewrite (cov2_beta_second_zero_iff_innovation a b c u v Ha Hd).
 symmetry; apply cov2_innovation_covariance_zero_iff; lra.
Qed.

(**
 [cov2_beta_second_noise_positive_preserved] (theorem) — Adding second-score measurement variance does not reverse the sign of a positive second-score regression slope.
 Mathematical meaning: Adding second-score measurement variance does not reverse the sign of a positive second-score regression slope.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (0<cov2_beta_second a (b+t) c u v <-> 0<cov2_beta_second a b c u v).
 Premises and side conditions: Original observed covariance positive definite and new diagonal variance nonnegative.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_second_noise_positive_preserved :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (0<cov2_beta_second a (b+t) c u v <-> 0<cov2_beta_second a b c u v).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 rewrite (cov2_beta_second_positive_iff_innovation a (b+t) c u v Ha Hdnew).
 rewrite (cov2_beta_second_positive_iff_innovation a b c u v Ha Hd).
 tauto.
Qed.

(**
 [cov2_beta_second_noise_negative_preserved] (theorem) — Adding second-test noise does not reverse the sign of a negative second regression coefficient.
 Mathematical meaning: Adding second-test noise does not reverse the sign of a negative second regression coefficient.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_beta_second a (b+t) c u v<0 <-> cov2_beta_second a b c u v<0).
 Premises and side conditions: Original positive-definite covariance and nonnegative measurement-noise variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_second_noise_negative_preserved :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> (cov2_beta_second a (b+t) c u v<0 <-> cov2_beta_second a b c u v<0).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 rewrite (cov2_beta_second_negative_iff_innovation a (b+t) c u v Ha Hdnew).
 rewrite (cov2_beta_second_negative_iff_innovation a b c u v Ha Hd).
 tauto.
Qed.

(**
 [cov2_beta_second_noise_exact_shrinkage] (theorem) — An explicit attenuation fraction relates the noisy second-test coefficient to its original least-squares coefficient.
 Mathematical meaning: An explicit attenuation fraction relates the noisy second-test coefficient to its original least-squares coefficient.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_beta_second a (b+t) c u v = cov2_beta_second a b c u v * (cov2_innovation_variance a b c / cov2_innovation_variance a (b+t) c).
 Premises and side conditions: Positive-definite covariance block and nonnegative diagonal noise ensure both innovation variances are nonzero.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_second_noise_exact_shrinkage :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_beta_second a (b+t) c u v = cov2_beta_second a b c u v * (cov2_innovation_variance a b c / cov2_innovation_variance a (b+t) c).
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 assert (Hvar:cov2_innovation_variance a b c<>0)
   by (pose proof (cov2_innovation_variance_positive a b c Ha Hd); lra).
 assert (Hnew:cov2_innovation_variance a (b+t) c<>0)
   by (pose proof (cov2_innovation_variance_positive a (b+t) c Ha Hdnew); lra).
 rewrite (cov2_beta_second_from_innovation a (b+t) c u v ltac:(lra) ltac:(lra)).
 rewrite (cov2_beta_second_from_innovation a b c u v ltac:(lra) ltac:(lra)).
 unfold Rdiv; field; split; assumption.
Qed.

(**
 [cov2_beta_first_noise_change_from_second] (theorem) — The first regression coefficient adjusts exactly to offset the change in the second coefficient under independent second-score noise.
 Mathematical meaning: The first regression coefficient adjusts exactly to offset the change in the second coefficient under independent second-score noise.
 Exact checked proposition: forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_beta_first a (b+t) c u v = cov2_beta_first a b c u v + c*(cov2_beta_second a b c u v-cov2_beta_second a (b+t) c u v)/a.
 Premises and side conditions: Positive first variance and positive original and inflated determinants.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_beta_first_noise_change_from_second :
 forall a b c u v t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_beta_first a (b+t) c u v = cov2_beta_first a b c u v + c*(cov2_beta_second a b c u v-cov2_beta_second a (b+t) c u v)/a.
Proof.
 intros a b c u v t Ha Hd Ht.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 rewrite (cov2_beta_first_after_partialing a (b+t) c u v ltac:(lra) ltac:(lra)).
 rewrite (cov2_beta_first_after_partialing a b c u v ltac:(lra) ltac:(lra)).
 unfold Rdiv; ring.
Qed.

(**
 [cov2_schur_noise_first_upper_one_test] (theorem) — The optimal two-score predictor with first-test noise is never worse than discarding test one.
 Mathematical meaning: The optimal two-score predictor with first-test noise is never worse than discarding test one.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur (a+t) b c u v s<=cov2_one_risk b v s.
 Premises and side conditions: Second test variance positive; observed block determinant positive; first noise nonnegative.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_upper_one_test :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur (a+t) b c u v s<=cov2_one_risk b v s.
Proof.
 intros a b c u v s t Hb Hd Ht.
 rewrite (cov2_schur_swap (a+t) b c u v s).
 apply cov2_schur_noise_second_upper_one_test; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_first_sandwich] (theorem) — With first-test noise, the best two-test risk lies between the original optimum and the second-test-only optimum.
 Mathematical meaning: With first-test noise, the best two-test risk lies between the original optimum and the second-test-only optimum.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur (a+t) b c u v s /\ cov2_schur (a+t) b c u v s<=cov2_one_risk b v s.
 Premises and side conditions: Positive second test variance, positive covariance determinant and nonnegative first noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_sandwich :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur a b c u v s<=cov2_schur (a+t) b c u v s /\ cov2_schur (a+t) b c u v s<=cov2_one_risk b v s.
Proof.
 intros a b c u v s t Hb Hd Ht; split.
 - apply cov2_schur_noise_first_monotone; assumption.
 - apply cov2_schur_noise_first_upper_one_test; assumption.
Qed.

(**
 [cov2_schur_noise_first_bound_old_slope] (theorem) — Original first regression weight supplies a quantitative upper bound on risk inflation caused by first-test noise.
 Mathematical meaning: Original first regression weight supplies a quantitative upper bound on risk inflation caused by first-test noise.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur (a+t) b c u v s<=cov2_schur a b c u v s+t*cov2_beta_first a b c u v*cov2_beta_first a b c u v.
 Premises and side conditions: Positive second variance and positive original determinant; noise nonnegative.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_bound_old_slope :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur (a+t) b c u v s<=cov2_schur a b c u v s+t*cov2_beta_first a b c u v*cov2_beta_first a b c u v.
Proof.
 intros a b c u v s t Hb Hd Ht.
 rewrite (cov2_schur_swap (a+t) b c u v s).
 rewrite (cov2_schur_swap a b c u v s).
 rewrite (cov2_beta_swap_second a b c u v).
 apply cov2_schur_noise_second_bound_by_old_slope; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_first_zero_partial] (theorem) — First-score noise has no effect when its partial target-signal numerator is exactly zero.
 Mathematical meaning: First-score noise has no effect when its partial target-signal numerator is exactly zero.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> b*u=c*v -> cov2_schur (a+t) b c u v s=cov2_schur a b c u v s.
 Premises and side conditions: Positive covariance determinant and positive second variance.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_zero_partial :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> b*u=c*v -> cov2_schur (a+t) b c u v s=cov2_schur a b c u v s.
Proof.
 intros a b c u v s t Hb Hd Ht Hpartial.
 apply (proj2 (cov2_schur_noise_first_eq_iff a b c u v s t Hb Hd Ht)).
 right; exact Hpartial.
Qed.

(**
 [cov2_schur_noise_first_nonnegative] (theorem) — Nonnegative optimal residual variance is preserved by independent noise on the first score.
 Mathematical meaning: Nonnegative optimal residual variance is preserved by independent noise on the first score.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=cov2_schur a b c u v s -> 0<=cov2_schur (a+t) b c u v s.
 Premises and side conditions: Positive-definite observed covariance, initial nonnegative residual, and nonnegative noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_nonnegative :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=cov2_schur a b c u v s -> 0<=cov2_schur (a+t) b c u v s.
Proof.
 intros a b c u v s t Hb Hd Ht Hnon.
 pose proof (cov2_schur_noise_first_monotone a b c u v s t Hb Hd Ht) as Hmono.
 lra.
Qed.

(**
 [cov2_schur_noise_second_below_unconditional] (theorem) — Even after second-score noise, optimized linear prediction is no worse than ignoring both scores.
 Mathematical meaning: Even after second-score noise, optimized linear prediction is no worse than ignoring both scores.
 Exact checked proposition: forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a (b+t) c u v s<=s.
 Premises and side conditions: Positive-definite observed covariance and nonnegative second-score noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_second_below_unconditional :
 forall a b c u v s t, 0<a -> 0<cov2_det a b c -> 0<=t -> cov2_schur a (b+t) c u v s<=s.
Proof.
 intros a b c u v s t Ha Hd Ht.
 apply cov2_schur_le_unconditional; [exact Ha|].
 apply cov2_det_noise_second_positive; assumption.
Qed.

(**
 [cov2_schur_noise_first_below_unconditional] (theorem) — Even after noise on the first test, best linear residual risk does not exceed unconditional target variance.
 Mathematical meaning: Even after noise on the first test, best linear residual risk does not exceed unconditional target variance.
 Exact checked proposition: forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur (a+t) b c u v s<=s.
 Premises and side conditions: Positive original second variance and covariance determinant; nonnegative first noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_below_unconditional :
 forall a b c u v s t, 0<b -> 0<cov2_det a b c -> 0<=t -> cov2_schur (a+t) b c u v s<=s.
Proof.
 intros a b c u v s t Hb Hd Ht.
 rewrite (cov2_schur_swap (a+t) b c u v s).
 apply cov2_schur_noise_second_below_unconditional; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_both_below_unconditional] (theorem) — Arbitrarily large finite independent diagonal noise still permits the zero predictor and hence cannot make the optimal linear residual exceed unconditional variance.
 Mathematical meaning: Arbitrarily large finite independent diagonal noise still permits the zero predictor and hence cannot make the optimal linear residual exceed unconditional variance.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur (a+t) (b+w) c u v s<=s.
 Premises and side conditions: Both original diagonal variances and determinant strictly positive; both noise variances nonnegative.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_both_below_unconditional :
 forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur (a+t) (b+w) c u v s<=s.
Proof.
 intros a b c u v s t w Ha Hb Hd Ht Hw.
 assert (Hdnew:0<cov2_det (a+t) (b+w) c)
   by (apply cov2_det_noise_both_positive; assumption).
 apply cov2_schur_le_unconditional; [lra|exact Hdnew].
Qed.

(**
 [cov2_schur_noise_both_sandwich] (theorem) — Two-sided information bound for simultaneous independent diagonal noise inflation.
 Mathematical meaning: Two-sided information bound for simultaneous independent diagonal noise inflation.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur a b c u v s<=cov2_schur (a+t) (b+w) c u v s /\ cov2_schur (a+t) (b+w) c u v s<=s.
 Premises and side conditions: Original positive-definite two-score covariance; nonnegative noise in both scores.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_both_sandwich :
 forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur a b c u v s<=cov2_schur (a+t) (b+w) c u v s /\ cov2_schur (a+t) (b+w) c u v s<=s.
Proof.
 intros a b c u v s t w Ha Hb Hd Ht Hw; split.
 - apply cov2_schur_noise_both_monotone; assumption.
 - apply cov2_schur_noise_both_below_unconditional; assumption.
Qed.

(**
 [cov2_schur_noise_both_old_slope_upper] (theorem) — Noise-induced inflation of optimal residual risk is bounded by the sum of independent noise variances weighted by squared original regression coefficients.
 Mathematical meaning: Noise-induced inflation of optimal residual risk is bounded by the sum of independent noise variances weighted by squared original regression coefficients.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur (a+t) (b+w) c u v s <= cov2_schur a b c u v s + t*cov2_beta_first a b c u v*cov2_beta_first a b c u v + w*cov2_beta_second a b c u v*cov2_beta_second a b c u v.
 Premises and side conditions: Positive-definite original covariance and nonnegative independent noise variances.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_both_old_slope_upper :
 forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> cov2_schur (a+t) (b+w) c u v s <= cov2_schur a b c u v s + t*cov2_beta_first a b c u v*cov2_beta_first a b c u v + w*cov2_beta_second a b c u v*cov2_beta_second a b c u v.
Proof.
 intros a b c u v s t w Ha Hb Hd Ht Hw.
 assert (Hdnew:0<cov2_det (a+t) (b+w) c)
   by (apply cov2_det_noise_both_positive; assumption).
 set (p:=cov2_beta_first a b c u v).
 set (q:=cov2_beta_second a b c u v).
 pose proof (cov2_risk_minimizer (a+t) (b+w) c u v s p q ltac:(lra) Hdnew) as Hminimum.
 pose proof (cov2_risk_noise_both a b c u v s p q t w) as Hshift.
 pose proof (cov2_risk_at_optimum a b c u v s ltac:(lra)) as Hopt.
 change (cov2_risk a b c u v s p q=cov2_schur a b c u v s) in Hopt.
 lra.
Qed.

(**
 [cov2_schur_noise_both_strict_if_first_partial] (theorem) — Positive first-score measurement noise strictly raises overall optimal risk if its original residual signal is nonzero, regardless of further nonnegative second-score noise.
 Mathematical meaning: Positive first-score measurement noise strictly raises overall optimal risk if its original residual signal is nonzero, regardless of further nonnegative second-score noise.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<t -> 0<=w -> b*u<>c*v -> cov2_schur a b c u v s<cov2_schur (a+t) (b+w) c u v s.
 Premises and side conditions: Both original diagonal variances and determinant positive; first noise strictly positive and second noise nonnegative.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_both_strict_if_first_partial :
 forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<t -> 0<=w -> b*u<>c*v -> cov2_schur a b c u v s<cov2_schur (a+t) (b+w) c u v s.
Proof.
 intros a b c u v s t w Ha Hb Hd Ht Hw Hpartial.
 assert (Hd1:0<cov2_det (a+t) b c).
 { apply cov2_det_noise_first_positive; try assumption; lra. }
 pose proof (cov2_schur_noise_first_strict_if_partial a b c u v s t Hb Hd Ht Hpartial) as Hstrict.
 pose proof (cov2_schur_noise_second_monotone (a+t) b c u v s w ltac:(lra) Hd1 Hw) as Hweak.
 lra.
Qed.

(**
 [cov2_schur_noise_both_strict_if_second_partial] (theorem) — Positive noise on the second score strictly worsens globally optimized prediction if the score carried partial information, even with additional first-score noise.
 Mathematical meaning: Positive noise on the second score strictly worsens globally optimized prediction if the score carried partial information, even with additional first-score noise.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<w -> a*v<>c*u -> cov2_schur a b c u v s<cov2_schur (a+t) (b+w) c u v s.
 Premises and side conditions: Positive original covariance minors, strictly positive second noise and nonnegative first noise.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_both_strict_if_second_partial :
 forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<w -> a*v<>c*u -> cov2_schur a b c u v s<cov2_schur (a+t) (b+w) c u v s.
Proof.
 intros a b c u v s t w Ha Hb Hd Ht Hw Hpartial.
 assert (Hd1:0<cov2_det a (b+w) c).
 { apply cov2_det_noise_second_positive; try assumption; lra. }
 pose proof (cov2_schur_noise_second_strict_if_partial a b c u v s w Ha Hd Hw Hpartial) as Hstrict.
 pose proof (cov2_schur_noise_first_monotone a (b+w) c u v s t ltac:(lra) Hd1 Ht) as Hweak.
 lra.
Qed.

(**
 [cov2_schur_noise_both_nonnegative] (theorem) — Nonnegative optimal residual variance remains nonnegative under simultaneous independent noise on both observed tests.
 Mathematical meaning: Nonnegative optimal residual variance remains nonnegative under simultaneous independent noise on both observed tests.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> 0<=cov2_schur a b c u v s -> 0<=cov2_schur (a+t) (b+w) c u v s.
 Premises and side conditions: Positive original covariance determinant and both nonnegative noise variances.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_both_nonnegative :
 forall a b c u v s t w, 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> 0<=cov2_schur a b c u v s -> 0<=cov2_schur (a+t) (b+w) c u v s.
Proof.
 intros a b c u v s t w Ha Hb Hd Ht Hw Hnon.
 pose proof (cov2_schur_noise_both_monotone a b c u v s t w Ha Hb Hd Ht Hw).
 lra.
Qed.

(**
 [cov2_schur_noise_second_level_order] (theorem) — Optimal linear residual risk is ordered by second-test measurement-noise level, not only by its comparison with zero noise.
 Mathematical meaning: Optimal linear residual risk is ordered by second-test measurement-noise level, not only by its comparison with zero noise.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<cov2_det a b c -> 0<=t -> t<=w -> cov2_schur a (b+t) c u v s<=cov2_schur a (b+w) c u v s.
 Premises and side conditions: Noise levels nonnegative and ordered; original covariance positive definite.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_second_level_order :
 forall a b c u v s t w, 0<a -> 0<cov2_det a b c -> 0<=t -> t<=w -> cov2_schur a (b+t) c u v s<=cov2_schur a (b+w) c u v s.
Proof.
 intros a b c u v s t w Ha Hd Ht Htw.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 pose proof (cov2_schur_noise_second_monotone
   a (b+t) c u v s (w-t) Ha Hdnew ltac:(lra)) as Hmono.
 replace (b+t+(w-t)) with (b+w) in Hmono by ring.
 exact Hmono.
Qed.

(**
 [cov2_schur_noise_first_level_order] (theorem) — Optimal linear prediction risk is ordered by the noise level of the first test.
 Mathematical meaning: Optimal linear prediction risk is ordered by the noise level of the first test.
 Exact checked proposition: forall a b c u v s t w, 0<b -> 0<cov2_det a b c -> 0<=t -> t<=w -> cov2_schur (a+t) b c u v s<=cov2_schur (a+w) b c u v s.
 Premises and side conditions: Positive second variance, determinant positive and nonnegative ordered noise levels.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_level_order :
 forall a b c u v s t w, 0<b -> 0<cov2_det a b c -> 0<=t -> t<=w -> cov2_schur (a+t) b c u v s<=cov2_schur (a+w) b c u v s.
Proof.
 intros a b c u v s t w Hb Hd Ht Htw.
 rewrite (cov2_schur_swap (a+t) b c u v s).
 rewrite (cov2_schur_swap (a+w) b c u v s).
 apply cov2_schur_noise_second_level_order; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_second_level_strict] (theorem) — Strict degradation of optimized prediction between two second-test noise levels holds whenever the extra noise is positive and the test carries residual target information.
 Mathematical meaning: Strict degradation of optimized prediction between two second-test noise levels holds whenever the extra noise is positive and the test carries residual target information.
 Exact checked proposition: forall a b c u v s t w, 0<a -> 0<cov2_det a b c -> 0<=t -> t<w -> a*v<>c*u -> cov2_schur a (b+t) c u v s<cov2_schur a (b+w) c u v s.
 Premises and side conditions: Original positive covariance determinant, ordered nonnegative noise levels and nonzero partial signal.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_second_level_strict :
 forall a b c u v s t w, 0<a -> 0<cov2_det a b c -> 0<=t -> t<w -> a*v<>c*u -> cov2_schur a (b+t) c u v s<cov2_schur a (b+w) c u v s.
Proof.
 intros a b c u v s t w Ha Hd Ht Htw Hpartial.
 assert (Hdnew:0<cov2_det a (b+t) c)
   by (apply cov2_det_noise_second_positive; assumption).
 pose proof (cov2_schur_noise_second_strict_if_partial
   a (b+t) c u v s (w-t) Ha Hdnew ltac:(lra) Hpartial) as Hstrict.
 replace (b+t+(w-t)) with (b+w) in Hstrict by ring.
 exact Hstrict.
Qed.

(**
 [cov2_schur_noise_first_level_strict] (theorem) — Strict degradation of optimal prediction between two first-score noise levels under nonzero first partial information.
 Mathematical meaning: Strict degradation of optimal prediction between two first-score noise levels under nonzero first partial information.
 Exact checked proposition: forall a b c u v s t w, 0<b -> 0<cov2_det a b c -> 0<=t -> t<w -> b*u<>c*v -> cov2_schur (a+t) b c u v s<cov2_schur (a+w) b c u v s.
 Premises and side conditions: Positive original second variance and determinant, strictly ordered positive noise increment.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_first_level_strict :
 forall a b c u v s t w, 0<b -> 0<cov2_det a b c -> 0<=t -> t<w -> b*u<>c*v -> cov2_schur (a+t) b c u v s<cov2_schur (a+w) b c u v s.
Proof.
 intros a b c u v s t w Hb Hd Ht Htw Hpartial.
 rewrite (cov2_schur_swap (a+t) b c u v s).
 rewrite (cov2_schur_swap (a+w) b c u v s).
 apply cov2_schur_noise_second_level_strict; try assumption.
 rewrite <- cov2_det_symmetric; exact Hd.
Qed.

(**
 [cov2_schur_noise_both_level_order] (theorem) — Monotonicity of best linear prediction risk in the two-dimensional partial order of independent measurement-noise levels.
 Mathematical meaning: Monotonicity of best linear prediction risk in the two-dimensional partial order of independent measurement-noise levels.
 Exact checked proposition: forall a b c u v s t w t' w', 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> t<=t' -> w<=w' -> cov2_schur (a+t) (b+w) c u v s<=cov2_schur (a+t') (b+w') c u v s.
 Premises and side conditions: Positive-definite original covariance; nonnegative initial noise and componentwise ordered noise increments.
 Proof/definition method: Combine the existing covariance Schur identities, normalized two-score innovations, positive-definite regression minimizer, determinant noise perturbations, and exact finite real algebra. Crucial comparisons explicitly reuse checked prior lemmas and discharge all nonzero/positive denominators.
 Library reuse: Rocq Stdlib.Reals, Lra, Psatz, Ring/Field, Rle_0_sqr, and existing TwoObservationSchur results. No custom matrix inverse, normal integral, or additional axioms.
 Boundary: Exact covariance and best-linear-prediction sensitivity only; stochastic independence of noise, Gaussian conditional distributions, normal tails, or empirical IQ test calibration are not proved.
 *)
Theorem cov2_schur_noise_both_level_order :
 forall a b c u v s t w t' w', 0<a -> 0<b -> 0<cov2_det a b c -> 0<=t -> 0<=w -> t<=t' -> w<=w' -> cov2_schur (a+t) (b+w) c u v s<=cov2_schur (a+t') (b+w') c u v s.
Proof.
 intros a b c u v s t w t' w' Ha Hb Hd Ht Hw Htt Hww.
 assert (Hdnew:0<cov2_det (a+t) (b+w) c)
   by (apply cov2_det_noise_both_positive; assumption).
 pose proof (cov2_schur_noise_both_monotone
   (a+t) (b+w) c u v s (t'-t) (w'-w)
   ltac:(lra) ltac:(lra) Hdnew ltac:(lra) ltac:(lra)) as Hmono.
 replace (a+t+(t'-t)) with (a+t') in Hmono by ring.
 replace (b+w+(w'-w)) with (b+w') in Hmono by ring.
 exact Hmono.
Qed.

