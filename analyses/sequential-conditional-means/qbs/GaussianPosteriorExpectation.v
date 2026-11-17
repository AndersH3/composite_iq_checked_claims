(** Module: GaussianPosteriorExpectation.v
 Purpose: Prove the genuine Lebesgue integral of the Gaussian posterior
 random parameter equals MathComp-Analysis's normal-normal conjugate
 posterior center. This is a measure-theoretic result, not a density
 square-completion or a postulated Gaussian mean axiom.
 Mathematical model: prior theta ~ N(m0, s0^2), normal likelihood
 observation x|theta ~ N(theta, s^2), and normalized conjugate posterior
 N(post_mean m0 s0 x s, post_stddev s0 s).
 Exact assumptions: the conjugate posterior standard deviation is nonzero,
 as holds from s0 != 0 and s != 0 by the upstream post_stddev_gt0 lemma.
 Library reuse: MathComp-Analysis normal_distribution for the posterior
 mean and variance parameters, and QBS.normal_centred.integral_normal_mean
 for the complete Lebesgue expectation integral. Neither library normal
 density integration nor Bayesian conjugacy is reconstructed.
 Scope: This identity establishes the conditional posterior *kernel*
 first moment at a fixed observation. The stronger claim about an
 arbitrary multivariate jointly Gaussian vector's conditional
 expectation on its entire observed sigma-algebra requires a
 disintegration/independence bridge not proved in this module.
 Verification: pinned Rocq 9.2, MathComp-Analysis 1.18 and an exact
 revision of LLM4Rocq/mathcomp-qbs (CeCILL-C; external source unmodified).
 Researcher/requester: Anders Hellström.
 AI disclosure: Theorem integration and source AI-assisted; only exact
 Rocq kernel compilation establishes verification.
*)
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import classical_sets reals ereal topology normedtype.
From mathcomp Require Import measure lebesgue_integral lebesgue_stieltjes_measure
  measurable_realfun.
From mathcomp.analysis Require Import normal_distribution.
From QBS Require Import normal_centred.
Require Import GaussianPosteriorMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import MeasurableR.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section GaussianPosteriorFirstMoment.
Context {R : realType}.

(** [gqbs_conjugate_posterior_expectation] (theorem).
 Mathematical meaning: integrating the identity variable against the
 *properly normalized posterior probability measure* returns its
 conjugate mean parameter. The integral exists and is finite by the
 maintained QBS normal-moment proof, not because a posterior mean is
 simply assigned by definition.
 Exact Rocq conclusion: integral of t against
 normal_prob(post_mean m0 sigma0 x sigma,post_stddev sigma0 sigma)
 equals the finite extended real post_mean m0 sigma0 x sigma.
 Required hypothesis: nondegenerate posterior standard deviation.
 Proof method: instantiate QBS's kernel-checked integral_normal_mean.
 Reuse: MathComp's post_mean, post_stddev, normal_prob,
 QBS.normal_centred.integral_normal_mean.
 Scope boundary: Conditional posterior kernel expectation for one
 Gaussian observation, not the universal full-history CE identity.
*)
Theorem gqbs_conjugate_posterior_expectation
    (m0 sigma0 x sigma : R) :
  post_stddev sigma0 sigma != 0 ->
  (\int[normal_prob (post_mean m0 sigma0 x sigma)
                       (post_stddev sigma0 sigma)]_t t%:E =
   (post_mean m0 sigma0 x sigma)%:E)%E.
Proof.
exact: integral_normal_mean.
Qed.

(** [gqbs_report_posterior_mean_integral] (theorem).
 Mathematical meaning: The *actual first moment integral* of the
 normalized conditional posterior Gaussian probability measure for
 the equicorrelated latent-factor sufficient-statistic model equals
 the report's exact predictor c*S_n / (1+(n-1)c).
 This joins the previously kernel-checked Gaussian conjugacy parameter
 identity to QBS's genuine normal first-moment integral.
 Explicit assumptions: nonzero prior/likelihood standard deviations
 and observed count; both standard deviations have the variance values
 specified by the latent common-factor model; denominators are nonzero.
 We do not hypothesize a conditional expectation; its value is derived
 as a Lebesgue probability integral of the normalized posterior.
 Scope: The fixed-observation posterior kernel, not the universal event
 integral over the full-history sigma-algebra of an arbitrary jointly
 Gaussian vector. Negative c is excluded by sigma0 squared = c,
 except the singular c=0 case, which requires a separate construction.
 Reuse: gmc_sufficient_statistic_posterior_center, maintained
 MathComp normal_distribution.post_stddev_gt0,
 gqbs_conjugate_posterior_expectation.
*)
Theorem gqbs_report_posterior_mean_integral
    (c n total sigma0 sigma : R) :
  n != 0 ->
  sigma0 != 0 ->
  sigma != 0 ->
  sigma0 ^+ 2 = c ->
  sigma ^+ 2 = (1-c)/n ->
  c + (1-c)/n != 0 ->
  1+(n-1)*c != 0 ->
  (\int[normal_prob (c*total/(1+(n-1)*c))
                      (post_stddev sigma0 sigma)]_t t%:E =
   (c*total/(1+(n-1)*c))%:E)%E.
Proof.
move=> Hn Hprior_nz Hnoise_nz Hprior Hnoise Haux Hd.
have Hmean : post_mean 0 sigma0 (total/n) sigma =
             c*total/(1+(n-1)*c).
  exact: (@gmc_sufficient_statistic_posterior_center
            R c n total sigma0 sigma Hn Hprior Hnoise Haux Hd).
rewrite -Hmean.
apply: gqbs_conjugate_posterior_expectation.
have Hpositive : 0 < post_stddev sigma0 sigma.
  exact: (post_stddev_gt0 Hprior_nz Hnoise_nz).
by rewrite (gt_eqF Hpositive).
Qed.

End GaussianPosteriorFirstMoment.
