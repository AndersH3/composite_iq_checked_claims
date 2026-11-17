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
From mathcomp Require Import measure lebesgue_integral.
From mathcomp.analysis Require Import normal_distribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section EquicorrelatedGaussianPosterior.
Context {R : realType}.
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
  exact: (gmc_sufficient_statistic_posterior_center Hn Hprior Hnoise
             Haux Hd).
rewrite -Hmean.
exact: (normal_prob_conjugate Hprior_nz Hnoise_nz mV).
Qed.

End EquicorrelatedGaussianPosterior.
