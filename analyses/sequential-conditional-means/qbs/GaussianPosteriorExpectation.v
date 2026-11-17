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

End GaussianPosteriorFirstMoment.
