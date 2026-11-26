(** Module: GaussianPosteriorMeasure.v
 Purpose: Connect the report's equicorrelated Gaussian forecast parameters to
 a genuine normalized posterior probability measure using the established
 MathComp-Analysis normal_prob_conjugate theorem, not merely an unnormalized
 exponential kernel or a newly postulated Gaussian conditioning axiom.
 Mathematical representation: c is the latent shared-factor variance, n
 the positive number of observed scores represented as a real scalar, and
 total their sum. Conditional on the latent factor theta the observed
 *sample mean* has noise standard deviation sigma, satisfying
 sigma^2=(1-c)/n. The Gaussian prior has sigma0^2=c.
 Explicit hypotheses: Nonzero sample size, prior and likelihood standard
 deviations, their stated squares and the relevant denominator
 conditions. Real mean/variance parameters are generic MathComp realType.
 The single-statistic normal-likelihood construction is used directly;
 sufficiency of this statistic for the complete score vector is a
 separate formalization obligation, despite the Stdlib square completion.
 Library use: MathComp-Analysis normal_prob_conjugate, post_mean and
 post_stddevE; MathComp algebra field_tactic. Do not reimplement
 Lebesgue integration, normal densities, normal measure normalization,
 finite sums or conditional probability from first principles.
 Limitations: The posterior formula is a genuine normalized probability
 measure for ONE Gaussian sample-mean observation as specified. The
 theorem does NOT construct a jointly normal n-vector or prove the
 sigma(X1,...,Xn) conditional expectation of the future random variable.
 Reproduction: .github/workflows/gaussian-mathcomp.yml with Rocq 9.2.0
 and the pinned MathComp-Analysis 1.18.0 released library.
 AI disclosure: AI-assisted specifications and proof source; only
 kernel-accepted results count as formally checked.
*)
From mathcomp Require Import boot order ssralg ssrnum field_tactic.
From mathcomp Require Import classical_sets reals ereal topology normedtype.
From mathcomp Require Import measure lebesgue_integral lebesgue_stieltjes_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section EquicorrelatedGaussianPosterior.
Context {R : realType}.
(* Supply MathComp's Borel measurable sets on the real order topology. *)
Import MeasurableR.
Implicit Types (c n total sigma : R) (V : set R).

(** [gmc_sufficient_statistic_posterior_center] (theorem).
 Mathematical meaning: The MathComp-Analysis normal-normal conjugacy
 parameter reduces algebraically to c times the observed score sum divided
 by d_n(c)=1+(n-1)c when the likelihood is the Gaussian sample mean.
 Exact checked proposition: Under the stated variance, count and
 denominator hypotheses, post_mean 0 sigma0 (total/n) sigma equals
 c*total/(1+(n-1)*c).
 Premises and side conditions: The two standard-deviation squares are
 stated, n is nonzero, and both algebraic denominators are nonzero.
 Proof/definition method: Unfold MathComp post_mean and normalize in the
 maintained MathComp field tactic, without changing its definition.
 Library reuse: MathComp-Analysis normal_distribution.post_mean and
 MathComp field_tactic.
 Boundary: Identity between normal posterior *parameters*, not a proof
 of sample-mean normality, sufficient statistics or conditional expectation.
*)
Theorem gmc_sufficient_statistic_posterior_center
    c n total sigma0 sigma :
  n != 0 ->
  sigma0 ^+ 2 = c ->
  sigma ^+ 2 = (1-c)/n ->
  c + (1-c)/n != 0 ->
  1+(n-1)*c != 0 ->
  post_mean 0 sigma0 (total/n) sigma =
  c*total/(1+(n-1)*c).
Proof.
move=> Hn Hprior Hnoise Haux Hd.
rewrite /post_mean Hprior Hnoise mulr0 add0r.
by field; rewrite ?Hn ?Haux ?Hd.
Qed.

(** [gmc_sufficient_statistic_posterior_variance] (theorem).
 Mathematical meaning: The normalized Gaussian posterior distribution
 identified by normal-normal conjugacy has squared standard deviation
 c*(1-c)/d_n(c), exactly the report's latent-factor posterior variance.
 Exact checked proposition: Under the stated nonzero and variance
 hypotheses, post_stddev sigma0 sigma squared has that form.
 Premises and side conditions: Both input standard deviations and n,
 both Gaussian precision denominators, and d_n(c) are nonzero.
 Proof/definition method: Rewrite MathComp's independently proven
 post_stddevE identity and use its field tactic for parameter conversion.
 Library reuse: MathComp-Analysis post_stddevE; MathComp field_tactic.
 Boundary: Normal posterior variance *parameter*, not a measure-theoretic
 second-moment integral or a multivariate conditional variance.
*)
Theorem gmc_sufficient_statistic_posterior_variance
    c n sigma0 sigma :
  n != 0 ->
  sigma0 != 0 ->
  sigma != 0 ->
  sigma0 ^+ 2 = c ->
  sigma ^+ 2 = (1-c)/n ->
  c + (1-c)/n != 0 ->
  1+(n-1)*c != 0 ->
  (post_stddev sigma0 sigma) ^+ 2 =
  c*(1-c)/(1+(n-1)*c).
Proof.
move=> Hn Hprior_nz Hnoise_nz Hprior Hnoise Haux Hd.
rewrite (post_stddevE Hprior_nz Hnoise_nz).
rewrite Hprior Hnoise.
by field; rewrite ?Hn ?Haux ?Hd.
Qed.

(** [gmc_normalized_gaussian_sufficient_statistic_posterior] (theorem).
 Mathematical meaning: The Bayesian posterior for the latent shared normal
 factor, given a Gaussian observation of the history sample mean, is a
 properly normalized normal *measure* with the report's predictor center.
 Exact checked proposition: The ratio of the prior normal measure's
 likelihood-weighted integral on V to the evidence integral over all
 theta equals normal_prob(c*total/d_n(c),post_stddev sigma0 sigma) V.
 Premises and side conditions: All Gaussian variances, sample count,
 denominators and the target event's measurability are explicit.
 Proof/definition method: Invoke the independently kernel-proven
 MathComp-Analysis normal_prob_conjugate integral identity, then use the
 previously checked exact posterior-center formula to identify report
 parameters; no self-proved integral, disintegration, or probability axiom.
 Library reuse: MathComp-Analysis normal_prob_conjugate, post_mean,
 normal_prob and normal_pdf, with MathComp real fields.
 Boundary: Normalized posterior law for the *single sufficient-score-mean
 observation model*. Extension to arbitrary full-history joint Gaussian
 vectors and conditional expectations remains a separate Rocq theorem.
*)
Theorem gmc_normalized_gaussian_sufficient_statistic_posterior
    c n total sigma0 sigma V :
  n != 0 ->
  sigma0 != 0 ->
  sigma != 0 ->
  sigma0 ^+ 2 = c ->
  sigma ^+ 2 = (1-c)/n ->
  c + (1-c)/n != 0 ->
  1+(n-1)*c != 0 ->
  measurable V ->
  ((\int[normal_prob 0 sigma0]_(t in V)
        (normal_pdf t sigma (total/n))%:E) /
    \int[normal_prob 0 sigma0]_t
        (normal_pdf t sigma (total/n))%:E =
    normal_prob (c*total/(1+(n-1)*c))
      (post_stddev sigma0 sigma) V)%E.
Proof.
move=> Hn Hprior_nz Hnoise_nz Hprior Hnoise Haux Hd mV.
have Hmean : post_mean 0 sigma0 (total/n) sigma =
             c*total/(1+(n-1)*c).
  apply: gmc_sufficient_statistic_posterior_center.
  - exact: Hn.
  - exact: Hprior.
  - exact: Hnoise.
  - exact: Haux.
  - exact: Hd.
rewrite -Hmean.
(* Explicitly instantiate every distributional parameter of the *existing*
   normalized posterior identity. The implicit-argument version failed
   proof-term inference even though the specialized type is identical
   to the goal (as confirmed by the pinned Rocq 9.2 diagnostic build).
   No density integral or posterior normalization is reimplemented. *)
exact: (@normal_prob_conjugate R 0 sigma0 sigma (total/n) V
           Hprior_nz Hnoise_nz mV).
Qed.

(** [gmc_normal_pdf_centered_residual] (theorem).
 Mathematical meaning: Evaluating the normal density at its mean plus a
 residual removes the location parameter. Exact representation:
 normal_pdf m s (m+e) = normal_pdf 0 s e.
 Premises and side conditions: Nonzero standard deviation, since the
 library's zero-scale fallback is not a Dirac density.
 Proof/definition method: Rewrite normal_pdfE and normal_fun, then
 cancel the translated center in the exponent.
 Library reuse: MathComp-Analysis normal_pdfE, normal_fun; MathComp addrK.
 Boundary: Pointwise equality only, not a change-of-variables theorem.
*)
Theorem gmc_normal_pdf_centered_residual m s e :
  s != 0 -> normal_pdf m s (m+e) = normal_pdf 0 s e.
Proof.
move=> Hs.
by rewrite !normal_pdfE // /normal_fun [m+e]addrC addrK subr0.
Qed.

(** [gmc_gaussian_observation_residual_density_factor] (theorem).
 Mathematical meaning: In the scalar Gaussian prior/noisy-observation
 construction, the joint density evaluated at a posterior-center-plus-
 residual coordinate factors into an observation density and a centered
 posterior-scale residual density.
 Exact representation: The prior-likelihood product at t=post_mean+e
 equals the product of the marginal observation normal density and the
 centered residual normal density.
 Premises and side conditions: Prior and noise scales are nonzero.
 Proof/definition method: Apply upstream pointwise normal conjugacy
 and the centered residual translation above.
 Library reuse: normal_pdf_conjugate, post_stddev_gt0, normal_pdfE.
 Boundary: Density factorization at transformed coordinates. A
 measure-level change of variables (unit Jacobian) and identification of
 the joint law are still needed to infer independent random variables.
*)
Theorem gmc_gaussian_observation_residual_density_factor m0 s0 s x e :
  s0 != 0 -> s != 0 ->
  normal_pdf (post_mean m0 s0 x s + e) s x *
    normal_pdf m0 s0 (post_mean m0 s0 x s + e) =
  normal_pdf m0 (Num.sqrt (s0 ^+ 2 + s ^+ 2)) x *
    normal_pdf 0 (post_stddev s0 s) e.
Proof.
move=> Hs0 Hs.
rewrite (@normal_pdf_conjugate R m0 s0 s x
  (post_mean m0 s0 x s + e) Hs0 Hs).
have Hp : post_stddev s0 s != 0.
  exact: lt0r_neq0 (post_stddev_gt0 Hs0 Hs).
by rewrite gmc_normal_pdf_centered_residual.
Qed.

(** [gmc_gaussian_observation_marginal_measure] (theorem).
 Mathematical meaning: Integrating the Gaussian likelihood measure
 over the normal prior gives the normalized marginal observation law.
 Exact representation: For measurable V, integrate normal_prob (m+t)
 s V under normal_prob m0 s0; the result has center m0+m and scale
 sqrt(s0^2+s^2).
 Premises and side conditions: Both scales nonzero; V measurable.
 Proof/definition method: Direct specialization of upstream convolution.
 Library reuse: MathComp-Analysis normal_probD.
 Boundary: This does not identify an arbitrary jointly Gaussian vector
 or prove its residual independence.
*)
Theorem gmc_gaussian_observation_marginal_measure m0 s0 m s V :
  s0 != 0 -> s != 0 -> measurable V ->
  (\int[normal_prob m0 s0]_t normal_prob (m+t) s V =
    normal_prob (m0+m) (Num.sqrt (s0 ^+ 2 + s ^+ 2)) V)%E.
Proof.
move=> Hs0 Hs mV.
exact: (@normal_probD R m0 s0 m s V Hs0 Hs mV).
Qed.

End EquicorrelatedGaussianPosterior.
