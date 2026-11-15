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
 pose proof (cov2_quad_positive_semidefinite a b c
   (cov2_beta_first a b c u v)
   (cov2_beta_second a b c u v) Ha Hd) as Hq.
 pose proof (cov2_beta_explained_quadratic a b c u v ltac:(lra)) as He.
 unfold cov2_schur.
 lra.
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
   assert (Hz:z=0) by nra.
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
 pose proof (cov2_one_to_two_gain a b c u v s ltac:(lra) ltac:(lra)) as Hg.
 assert (Hden:0<a*cov2_det a b c) by nra.
 assert (Hi:0< /(a*cov2_det a b c))
   by (apply Rinv_0_lt_compat; exact Hden).
 pose (z:=a*v-c*u).
 assert (Hz:z<>0) by (unfold z; lra).
 assert (Hsq:0<z*z) by nra.
 assert (Hgain:0<(a*v-c*u)*(a*v-c*u)/(a*cov2_det a b c)).
 { change (0<z*z/(a*cov2_det a b c)).
   unfold Rdiv; apply Rmult_lt_0_compat; assumption. }
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

