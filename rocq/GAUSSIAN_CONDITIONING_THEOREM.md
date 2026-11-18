# Gaussian conditioning for sequential equicorrelated scores

**AI DISCLOSURE — Prominent:** This mathematical explanation and its Rocq
implementation plan were written with AI assistance under the direction of
**Anders Hellström**. A conventional mathematical derivation is **not**
equivalent to a Rocq kernel proof. Check the corresponding exact Git commit
and CI results before treating a formal statement as proved.

**Verified D053–D056 checkpoint (November 17, 2026).** The
[Rocq 9.2 kernel workflow for D056](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/44153123270)
passed at commit `a4cb5346b25566687539556bf2de2fb57d5798f9`, following
[successful D053](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/44148837279),
[D054](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/44150279356)
and [D055](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/44151481763)
checks. This continuation adds **105 substantive named Rocq declarations**:
23 in `GaussianInnovationBounds.v`, 20 additional full-domain results in
that module, 30 in `GaussianBatchBalance.v`, and 32 in
`GaussianFiniteHistoryPosterior.v`. Together with the **187** previously
verified D050–D052 declarations, this gives **292 Gaussian-specific
kernel-checked declarations**. This is a count of exact theorem
statements—not 292 independent Gaussian-distribution laws. It does not
complete the measure-theoretic Gaussian conditional expectation or a
regular conditional law.

## Model and covariance-domain theorem

Let `m=n+k` be a finite positive number of standardized test scores, with
`n>=1`, `k>=1`, and let the full jointly Gaussian vector have mean zero,
variance one per coordinate, and common distinct-coordinate covariance `c`.
Its covariance is `Sigma_m(c)=(1-c)I_m+c 11^T`.

For `m>=2`, this covariance is PSD **if and only if**

```
-1/(m-1) <= c <= 1,
```

and PD precisely when both inequalities are strict. Its contrast eigenvalues
are `1-c` (multiplicity m-1) and its common eigenvalue is
`d_m(c)=1+(m-1)c`. The previously verified
`EquicorrelationVectors.vector_equicorrelation_psd_iff` and `pd_iff`
give an exact finite-real-list version; `GaussianCovarianceDomain.v`
checks the signed-correlation conditional Schur complement.

For the observed block `Sigma_n`, assume `c<1` and `d_n(c)>0`;
its inverse acts as

```
Sigma_n^-1 = (I_n - (c/d_n(c)) 11^T)/(1-c).
```

The `n=1` observed block is invertible as well, even at `c=1`,
but the displayed inverse formula uses `c<1`.

## Actual Gaussian conditional-expectation theorem (mathematical proof)

Set `S_n=sum(X_1,...,X_n)`. For any future score `Y=X_{n+1}`,

```
Cov(Y,X_1,...,X_n) = c 1_n^T.
beta = Cov(Y,X) Sigma_n^-1 = (c/d_n(c)) 1_n^T.
R = Y - beta X.
```

The covariance of `R` with **every** observed coordinate equals zero.
Since `(R,X_1,...,X_n)` is jointly Gaussian, a jointly Gaussian vector
with zero cross-covariance blocks has independent blocks. Therefore `R`
is independent of the entire observed sigma-algebra, has mean zero, and
has constant variance

```
Var(R) = 1 - n*c^2/d_n(c)
       = (1-c)*(1+n*c)/d_n(c).
```

Using independence and integrability of the Gaussian residual gives,
as a **measure-theoretic conditional expectation** (a.s.),

```
E[Y | sigma(X_1,...,X_n)] = c*S_n/d_n(c).
```

Moreover the regular conditional distribution of the future score, for
every observed vector in the natural Gaussian conditional kernel, is

```
Y | X=x ~ N(c*sum(x)/d_n(c), (1-c)*(1+n*c)/d_n(c)).
```

This proof depends decisively on the independently justified theorem
that uncorrelated jointly Gaussian subvectors are independent and on
standard existence/measurability facts for regular conditionals.
**The current Rocq project has NOT yet formalized that implication or
the regular-conditional-integral construction.** Algebraic minimization
and a pointwise normal-kernel completion alone cannot replace it.

For `k` future scores, their conditional mean vector is
`(c*S_n/d_n(c)) 1_k` and the conditional covariance matrix is

```
Sigma_future|observed = (1-c)I_k
                       + c*(1-c)/d_n(c) * 1_k 1_k^T.
```

Its contrast and common eigenvalues are, respectively,

```
1-c
(1-c)*d_(n+k)(c)/d_n(c).
```

The second identity, together with the precise feasibility constraints,
is the report-critical signed-correlation covariance-domain result checked
in `GaussianCovarianceDomain.v`. It remains valid when `c<0`, provided
the **full** covariance domain is satisfied.

## Positive-correlation conjugate Gaussian construction

For `0<c<1`, set independent `Theta~N(0,c)` and
`epsilon_i~N(0,1-c)` and define `X_i=Theta+epsilon_i`.
The posterior common signal, after observations `x_1,...,x_n`, is

```
Theta | X=x ~
 N(c*S_n/d_n(c), c*(1-c)/d_n(c)).
```

Indeed, completing the quadratic of the joint prior times likelihood gives

```
theta^2/c + sum_i (x_i-theta)^2/(1-c)
 = [d_n(c)/(c*(1-c))]*(theta-c*S_n/d_n(c))^2
   + [sum_i x_i^2-c*S_n^2/d_n(c)]/(1-c).
```

The Rocq module `GaussianConditionalKernel.v` checks this *pointwise*
completion and its unnormalized exponential factorization. An actual
posterior measure theorem additionally needs a Gaussian density-integral
normalization and moment theorem. [MathComp-Analysis'
`normal_prob_conjugate`](https://math-comp.github.io/analysis/htmldoc/1_19_0/mathcomp.analysis.probability_theory.normal_distribution.html)
provides a reusable, previously formalized normal-normal conjugacy
theorem. Future work must instantiate that library theorem for the
sufficient observed-score mean (or an iterated score likelihood) and
bridge it to Stdlib real `R` using the maintained MathComp
`reals-stdlib` compatibility library; it must not import a statement
as a new project axiom.

The independent-common-factor construction is not a representation of
negative pairwise correlation. Negative `c` must be treated through
the general jointly Gaussian covariance PSD/PD criterion above.

## D050 verification and full-history likelihood sufficiency

**AI disclosure:** The following kernel-level analysis and this
summary were AI-assisted. The mathematical proof of conditional
expectation discussed above remains distinct from a completed
formal measure-theoretic theorem.

The Rocq 9.2 corpus now contains [56 checked D050 theorems](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43997860735),
including exact finite-list density factorization

```
sum_i (x_i-theta)^2 =
  sum_i (x_i-mean(x))^2 + n*(theta-mean(x))^2,
```

and its multiplicative exponential likelihood factorization.
Two histories with equal lengths and sums have identical
latent-parameter posterior kernels after their data-only
evidence factors are divided out. This is a genuine
**pointwise sufficient-statistic** result for arbitrarily
unequal observed score lists; no empirical distribution
assumption is deduced from it.

Five further Rocq-verified covariance-domain results cover the **single
future-score case**: its Schur variance equals
`(1-c)*d_(r+1)(c)/d_r(c)`, with PSD and PD **if and only if**
the full r+1 covariance domain is respectively nonnegative and strict
for `r>=1` and `d_r(c)>0`. The admissible singular endpoints
`c=1` and `d_(r+1)(c)=0` both have exactly zero residual variance.
The existing concrete future-vector PSD/PD iff covers future
dimension at least two.

The separate MathComp-Analysis 1.18.0 source
`analyses/sequential-conditional-means/mathcomp/GaussianPosteriorMeasure.v`
specializes `normal_prob_conjugate` to the observed sample mean
and proposes a **normalized posterior probability measure**,
with parameter identities `c*S_n/d_n(c)` and
`c*(1-c)/d_n(c)`. Its CI must be green before those
three new theorems are counted as kernel verified.

To complete the formal Gaussian **conditional expectation**
for the full score history, the sample-mean likelihood
sufficiency factorization and this normalized measure theorem
must be connected in a common formal real/probability
representation. An independent proof of normal first moments,
the observed-score sigma-algebra conditional-expectation
universal property, and a jointly Gaussian model for all
admissible negative c are still required. Issue #50 records
those obligations.

## Singular covariance endpoints

At `c=1`, all standardized scores are equal almost surely, the observed
covariance is singular for `n>1`, and a deterministic conditional score
can be obtained directly without the displayed inverse. At the lower
endpoint `c=-1/(m-1)`, the full score sum is zero almost surely; the
conditional common future direction has variance zero. In the special
case `m=n+1`, the one future score equals `-S_n` almost surely.
Neither endpoint permits naïve use of inverse formulas with a zero
denominator.

## Full measure-theoretic conditional-expectation proof

**AI disclosure:** The following mathematical proof and the accompanying
formalization plan were AI-assisted. It is a conventional proof from
standard Gaussian measure theory, **not yet a single completed Rocq
proof** of the full vector-valued result. The existing kernel-tested
sublemmas are identified separately above.

**Theorem (Gaussian equicorrelation conditioning, including
semidefinite endpoints).** Let integers `n>=1`, `k>=1`,
`m=n+k`, and let `Z=(X_1,...,X_n,Y_1,...,Y_k)` be a (possibly
degenerate) centered jointly Gaussian random vector. Assume

```
Cov(Z)=Sigma_m(c)=(1-c)I_m + c*1_m*1_m^T,
-1/(m-1) <= c <= 1.
```

Write `S=sum_{i=1}^n X_i`, `d=1+(n-1)c`, and
`G=sigma(X_1,...,X_n)`. For any future index `j`,

```
E[Y_j | G] = (c/d)*S                          almost surely,
Cov(Y_future | G)
   = (1-c)I_k + c*(1-c)/d *1_k*1_k^T        almost surely.
```

The second identity uses the conditional covariance matrix defined
through conditional expectation of centered pairwise products. The
regular conditional law, as a version for every observed `x` in
the canonical Gaussian kernel, is the possibly degenerate
multivariate normal distribution with mean
`(c/d)*sum(x_i)*1_k` and this covariance.

**Proof for `c<1`.** Because `k>=1` and the full covariance is
positive semidefinite, the observed covariance block

```
A=(1-c)I_n+c*1_n*1_n^T
```

is positive definite, including at the lower singular endpoint of
the **full** covariance. Indeed `1-c>0`, and

```
d=1+(n-1)c >= 1-(n-1)/(m-1) = k/(m-1)>0.
```

The rank-one inverse formula is therefore valid:

```
A^-1=(I_n-(c/d)*1_n*1_n^T)/(1-c).
```

Let `B=c*1_k*1_n^T` be the future/observed cross-covariance block.
Direct calculation gives `BA^-1=(c/d)*1_k*1_n^T`.
Define the random-vector **innovation** (not an assumed conditional
expectation)

```
R=Y-(BA^-1)X.
```

This is an affine transformation of a jointly Gaussian vector;
hence the concatenated pair `(R,X)` is jointly Gaussian. Its
cross-covariance vanishes:

```
Cov(R,X)=B-BA^-1 A=0.
```

For real `t∈R^k`, `s∈R^n`, the characteristic function of
the jointly Gaussian pair is

```
E[exp(i*(t^T R+s^T X))]
 = exp(-1/2*(t^T D t+s^T A s)),
D=Cov(R)=Sigma_k(c)-BA^-1 B^T,
```

and the exponent has **no cross term** because `Cov(R,X)=0`.
The right-hand side factors into the characteristic functions
of `R` and `X`. Uniqueness of characteristic functions
therefore proves independence of `sigma(R)` and `G`.
This is the critical Gaussian-specific implication; mere zero
covariance does not imply independence for arbitrary distributions.

Each component of the Gaussian innovation is integrable, centered
and independent of `G`. Consequently for every `H∈G`,

```
E[R_j*1_H]=E[R_j]*P(H)=0.
```

The linear predictor `L=BA^-1 X=(c/d)*S*1_k` is
`G`-measurable and integrable. Thus, for every `H∈G`,

```
E[Y_j*1_H]=E[(L_j+R_j)*1_H]=E[L_j*1_H].
```

This is **exactly** the defining measure-theoretic universal property
of conditional expectation. Uniqueness in `L¹` yields
`E[Y_j|G]=L_j` almost surely.

For conditional covariance, `R` is independent of `G`,
so its centered second moments remain unconditional after conditioning.
The Schur calculation gives

```
D=Cov(R)
 = ((1-c)I_k+c*1_k*1_k^T)
   - n*c^2/d*1_k*1_k^T
 = (1-c)I_k+c*(1-c)/d*1_k*1_k^T.
```

This matrix may be merely positive semidefinite. Since `R` is a
(possibly degenerate) Gaussian vector independent of `X`,
translating its distribution by `L(x)` constructs a regular
conditional Gaussian kernel. This completes the `c<1` case.

**Proof at `c=1`.** All coordinate variances are one and all
pairwise covariances one, hence

```
Var(Z_i-Z_j)=2-2c=0.
```

A centered square-integrable random variable with zero variance
is constant almost surely, so all coordinates equal `X_1` almost
surely. Since `d=n` and `S=nX_1`, the predictor formula
`(c/d)*S=X_1` holds without attempting to invert the singular
matrix `A`. The conditional covariance is zero, consistent
with the Schur expression's factor `1-c=0`.

**Lower singular boundary.** If `c=-1/(m-1)`,
the full sum `T=sum_{i=1}^m Z_i` has variance
`m*d_m(c)=0`; hence `T=0` almost surely. The observed
block remains invertible for `k>=1`, so the first proof still
works. In particular `c/d=-1/k`, each future-score
conditional expectation is `-S/k`, and the future
conditional covariance has a zero all-ones eigenvalue.
When `k=1`, the only future score is exactly `-S`
almost surely.

**What the Rocq proof must establish.** The already checked
`GaussianCovarianceDomain.v` and
`EquicorrelationVectors.v` lemmas verify the algebraic
PSD/PD feasibility and Schur factorization, and
`GaussianConditionalKernel.v` verifies arbitrary-score
likelihood sufficiency. To obtain a complete kernel proof of
the above theorem, the probability-library integration
must additionally verify: closure of jointly Gaussian
vectors under linear transformation; characteristic-function
factorization implying **independence of sigma algebras**;
Gaussian finite first and second moments; the conditional
expectation universal property for every observed-measurable
event; and the degenerate `c=1` endpoint separately.
The independent-residual conditional expectation theorem
in the new FormalML module targets the fourth obligation
but requires the prior Gaussian independence step rather
than postulating the CE conclusion.

## Formal verification boundary and next proof obligation

A successful Rocq kernel check of the D050 sources certifies exactly their
real-list, covariance-Schur and Gaussian *pointwise density* propositions.
The measure-theoretic theorem still requires a verified Gaussian
probability space, multivariate normal closure under linear maps,
uncorrelated Gaussian blocks implying independence, and conditional
expectation or disintegration. Gaussian integration and posterior moments
should be reused from MathComp-Analysis rather than re-proved ad hoc.
Numerical Dask simulations cannot close this logical gap.

## Appendix — Complete AI disclosure

OpenAI ChatGPT assisted selection of theorems, derivation of covariance
and Gaussian formulas, Rocq proof generation and correction, library
investigation, documentation, source-order review, and GitHub operations.
The requester/researcher, Anders Hellström, supplied the research objective.
Rocq kernel checks establish only the exact propositions compiled at the
identified revision. The classical Gaussian conditioning argument relies on
known measure-theoretic results not yet integrated into this repository's
Rocq kernel proof. No new empirical human IQ data, Gaussian model
validation, probability calibration, independent peer review, or certified
Monte Carlo tail probability is claimed.
