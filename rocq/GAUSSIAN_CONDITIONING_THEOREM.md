# Gaussian conditioning for sequential equicorrelated scores

**AI DISCLOSURE — Prominent:** This mathematical explanation and its Rocq
implementation plan were written with AI assistance under the direction of
**Anders Hellström**. A conventional mathematical derivation is **not**
equivalent to a Rocq kernel proof. Check the corresponding exact Git commit
and CI results before treating a formal statement as proved.

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

## Singular covariance endpoints

At `c=1`, all standardized scores are equal almost surely, the observed
covariance is singular for `n>1`, and a deterministic conditional score
can be obtained directly without the displayed inverse. At the lower
endpoint `c=-1/(m-1)`, the full score sum is zero almost surely; the
conditional common future direction has variance zero. In the special
case `m=n+1`, the one future score equals `-S_n` almost surely.
Neither endpoint permits naïve use of inverse formulas with a zero
denominator.

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
