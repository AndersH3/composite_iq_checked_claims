# Combining IQ Scores: Analysis and a Corrected Version

Prepared 30 October 2026. This is an independently written statistical treatment, not a transcription of the source.

The [original article](https://megasociety.org/noesis/141/ferguson.html) is attributed to Ronald K. Hoeflin and reproduces George A. Ferguson’s treatment of variances and covariances. Its covariance algebra is correct. The problem is that an algebraically standardized composite does not, by itself, establish the population percentile or psychological interpretation assigned to it.

The principal corrections are these:

- The correlations used for standardization must describe the same reference population as the component scores. The article’s 27 selected high scorers do not establish the required population correlations.
- A composite’s mean and variance do not determine its extreme percentiles. A normal-tail calculation requires an additional distributional assumption.
- The 100-test entry should be approximately **3.69**, rather than **3.71**, standard deviations. Using the more accurate normal quantile also changes some final digits elsewhere.
- A standardized composite, an estimate of latent ability, and a validated IQ score have different interpretations. Their equivalence requires evidence.
- Rounded whole-number scores are approximate illustrations, not exact qualifying cutoffs.

The revised article follows. All numerical results below were recalculated independently.

---

**Combining IQ Test Scores: A Statistical Method and Its Limits**

Several cognitive test scores can be combined into a single score. The calculation must account for the tests’ correlations: correlated scores cannot be treated as independent when calculating the composite’s variance. The resulting composite also needs an explicit interpretation. Rescaling it to an IQ-style scale supplies units; evidence about the battery establishes what those units mean.

Before calculating a composite, specify the tests, their weights, the administration procedure, and the population against which scores will be compared. Composite construction and interpretation require their own justification; evidence supporting the individual tests does not automatically establish the meaning of their combination. This distinction is reflected in Standard 1.14 of the [AERA/APA/NCME Standards for Educational and Psychological Testing](https://www.testingstandards.net/uploads/7/6/6/4/76643089/9780935302356.pdf).

For test \(i\), convert the observed score \(x_i\) to a standardized score:

\[
z_i=\frac{x_i-\mu_i}{\sigma_i},
\]

where \(\mu_i\) and \(\sigma_i\) are its mean and standard deviation in the intended reference population. The norms must support comparison with that population. Using different numbers labelled “IQ” does not establish their comparability.

For example, a score of 160 on a scale with mean 100 and standard deviation 15 corresponds to \(z=4\). The same numerical score on a scale with standard deviation 16 corresponds to \(z=3.75\). These scores should be standardized before they are combined.

Let \(R\) be the population correlation matrix of the standardized test scores, and let \(w\) contain fixed weights. The weighted sum has variance

\[
\operatorname{Var}(w^\mathsf{T}Z)=w^\mathsf{T}Rw.
\]

Consequently, provided this variance is positive, a standardized composite is

\[
\boxed{Z_C=\frac{w^\mathsf{T}z}{\sqrt{w^\mathsf{T}Rw}}.}
\]

With the correct population parameters, this composite has mean zero and variance one. This statement requires finite variances, but does not require normality. When the parameters are estimated, their uncertainty affects the calibration of the composite.

For an equally weighted battery of \(n\) tests, write \(\bar z\) for the average standardized score and \(\bar r\) for the average correlation across the distinct pairs of tests. Then

\[
\begin{aligned}
\operatorname{Var}(\bar Z)
&=\frac{n+2\sum_{i<j}r_{ij}}{n^2}\\
&=\frac{1+(n-1)\bar r}{n}\\
&=\bar r+\frac{1-\bar r}{n}.
\end{aligned}
\]

Therefore,

\[
\boxed{Z_C=\frac{\bar z}{\sqrt{\bar r+(1-\bar r)/n}}.}
\]

Identical pairwise correlations are unnecessary for this variance identity; their average is sufficient for this particular equal-weight composite. The full matrix remains relevant to other weighting schemes and to understanding the battery.

An IQ-style reporting scale with mean 100 and standard deviation \(s\) can be defined by

\[
I_C=100+sZ_C.
\]

When all component scores already use mean 100 and the same standard deviation \(s\), the formula becomes

\[
I_C=100+\frac{\bar I-100}{\sqrt{\bar r+(1-\bar r)/n}},
\]

where \(\bar I\) is their arithmetic average.

For example, three scores averaging 160, each on an SD-16 scale, produce \(\bar z=3.75\). If their population average correlation is 0.60, then

\[
Z_C=\frac{3.75}{\sqrt{0.60+0.40/3}}
\approx4.3791,
\]

and the corresponding composite score is approximately 170.06 on the SD-16 reporting scale. This is a score on the specified composite. Interpreting it as a measure of general intelligence requires evidence about what the composite measures.

To assign a percentile, we also need the composite’s distribution. Mean zero and variance one do not make a distribution normal. Joint multivariate normality of the component scores is a sufficient condition for a fixed linear composite to be normal. Normal distributions for the individual tests alone are insufficient.

If a standard-normal distribution is justified for the composite, its percentile is \(100\Phi(Z_C)\), where \(\Phi\) is the standard-normal cumulative distribution function. A one-in-a-million upper-tail probability corresponds to

\[
q=\Phi^{-1}(0.999999)\approx4.7534243088.
\]

Thus the model-based 99.9999th-percentile threshold is

\[
\bar z_{\min}=q\sqrt{\bar r+\frac{1-\bar r}{n}}.
\]

The quantile can be reproduced with `qnorm(1e-6, lower.tail = FALSE)` in R; the [official R documentation](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/Normal.html) defines the normal quantile function and its upper-tail option.

For \(\bar r=0.60\), the thresholds are:

| Number of tests | Required average component z-score | Required average component score, mean 100 and SD 16 |
|---:|---:|---:|
| 1 | 4.7534 | 176.05 |
| 2 | 4.2516 | 168.03 |
| 3 | 4.0706 | 165.13 |
| 4 | 3.9770 | 163.63 |
| 5 | 3.9198 | 162.72 |
| 10 | 3.8027 | 160.84 |
| 100 | 3.6942 | 159.11 |
| 1,000 | 3.6832 | 158.93 |
| Limit as n increases | 3.6820 | 158.91 |

These are thresholds for the **average component score**, under the stated model. The target composite score remains approximately 176.05 on the SD-16 scale in every row. Values are rounded for display; an operational classification rule must specify rounding and use the appropriate attainable scores.

For an SD-15 reporting scale, use \(100+15\bar z_{\min}\) instead. In particular, the single-test threshold would be approximately 171.30. An IQ number without its scale convention is ambiguous.

The limiting average threshold follows from

\[
\lim_{n\to\infty}\bar z_{\min}=q\sqrt{\bar r},
\]

if the average correlation remains fixed as tests are added. With \(\bar r=0.60\), the limiting average component score on the SD-16 scale is approximately 158.91. This is a feature of the assumed sequence of batteries and its threshold; it is not a ceiling on possible composite scores. Adding tests can also change the average correlation, so the fixed-correlation limit should not be treated as a universal rule.

The choice of correlation matters substantially. For three tests, an average correlation of 0.90 raises the required average SD-16 component score to approximately 173.48, compared with 165.13 at 0.60. A smaller assumed correlation gives a larger composite score for the same positive average performance. The correlation therefore needs to be estimated for the relevant population and administration procedure. A lower correlation does not, by itself, establish better measurement; it can also reflect different constructs or greater measurement noise.

Correlations in a selected high-scoring sample need not equal correlations in the population used to standardize the tests. Selection can change score variances and relationships. The appropriate treatment depends on the selection mechanism and the information available about the unrestricted population; there is no universal adjustment. [Sackett and Yang’s methodological paper](https://pubmed.ncbi.nlm.nih.gov/10740961/) explains why range-restriction corrections depend on those details. A small selected sample cannot directly establish a one-in-a-million population frequency.

The scoring procedure also matters. A fixed battery, the best few results from many attempts, and a rule that keeps adding tests until someone qualifies have different score distributions. Each procedure requires calibration for the rule actually used. Repeated administrations can introduce practice effects, as documented in [Hausknecht and colleagues’ research synthesis](https://ecommons.cornell.edu/entities/publication/97becf46-3c0a-4de4-a48f-79b715ba8446). Repeated or overlapping tests should not be counted as fresh independent observations without accounting for their dependence and administration history.

Finally, variability across people is different from uncertainty about one person. The correlation matrix determines how the composite varies in the reference population. It does not, by itself, provide an individual confidence interval, separate general ability from shared methods, or establish measurement precision at extreme scores. Those questions require an appropriate measurement model and supporting data.

A defensible report should identify the battery, norms, weights, estimated correlations, and uncertainty. Direct composite norms should be used when they adequately support the intended interpretation. If an extreme percentile comes from a distributional model beyond the available normative evidence, report it as a model-based extrapolation and show how sensitive it is to the assumptions. The testing standards require clear descriptions of reference populations and norming procedures in Standards 5.8–5.9, and justification for score interpretations in Standards 1.1–1.4. [AERA/APA/NCME Standards](https://www.testingstandards.net/uploads/7/6/6/4/76643089/9780935302356.pdf).

---

**An optional mathematical illustration: composite scores and latent ability**

To see why these quantities differ, suppose, expressly as a hypothetical model, that

\[
Z_i=\sqrt{\rho}\,G+\sqrt{1-\rho}\,\varepsilon_i,
\]

where \(G\) and all \(\varepsilon_i\) are independent standard-normal variables and \(0<\rho<1\). This model treats all shared variance as one common factor and all residuals as mutually independent. Real batteries need not satisfy those assumptions.

In this particular model, the equal-weight composite’s squared correlation with \(G\) is

\[
\mathcal R=\frac{n\rho}{1+(n-1)\rho},
\]

and the conditional distribution of the latent factor has

\[
E[G\mid Z_1,\ldots,Z_n]=\sqrt{\mathcal R}\,Z_C,
\qquad
\operatorname{Var}(G\mid Z_1,\ldots,Z_n)
=\frac{1-\rho}{1+(n-1)\rho}.
\]

For three tests with \(\rho=0.60\), a composite at \(Z_C=4.7534\) has conditional mean \(G\) of approximately 4.30 and conditional standard deviation approximately 0.43. On a hypothetical latent scale with mean 100 and SD 16, these become a mean of approximately 168.79 and a standard deviation of 6.82. The composite’s reporting-scale value is approximately 176.05. The two values answer different questions, even in this unusually simple model.

The illustration is a mathematical counterexample to treating a standardized composite as automatically identical to a latent-ability estimate. It is not a proposed correction factor for actual IQ scores, and inter-test correlation should not generally be equated with reliability or common-factor variance.
