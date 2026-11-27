# IQ test differences: both report sources

**AI disclosure:** AI-assisted obligation-discovery index for Anders Hellström, baseline `e790af0559c716596d2d251af32057879689672c`. Each formal environment is indexed and mapped to the relevant proof packages. Every mathematical assertion needs an exact Rocq match; algebraic evidence is not full probability verification. Generated outputs are evidence; analytic targets, bounds and arithmetic need certificates.

## New IQ report obligations

| Proposition | Existing partial evidence | Remaining full claim | Packages |
|---|---|---|---|
| prop:moments | IQDifferenceAlgebra.iq_gap_variance; FiniteMoments | General L2 expectation/covariance and Cauchy–Schwarz, not merely scalar identity. | G01 |
| prop:domain | EquicorrelationVectors; IQDifferenceAlgebra.iq_equicorrelation_domain | PSD iff and actual iid-normal projection construction including singular endpoints. | G02 |
| prop:gap | IQDifferenceAlgebra.iq_gap_variance | Normal contrast law, half-normal CDF/first and second moments; zero-variance a.s. | G02 G14 G25 |
| prop:range | IQDifferenceAlgebra.iq_absolute_shift, iq_absolute_scale | Measurable extrema, iid maximum law, unique minimum a.s., range CDF and expectation integral. | G02 G14 G26 |
| prop:five | No matching full theorem identified | Integration by parts, density rescaling, three-way Gaussian orthant identity and exact a5. | G26 G27 |
| prop:mixtures | IQDifferenceAlgebra.iq_weighted_scale_jensen_deficit, iq_weighted_scale_jensen_strict, iq_shared_mixture_average, iq_smooth_mixture_average | General mixture kernel, unchanged normal margins, total covariance and strict Jensen for nonconstant mixing. | G01 G05 G06 G25 G26 G28 |
| prop:block | IQDifferenceAlgebra.iq_block_average | Actual replicated Gaussian pair law, range and pair-average distinction. | G25 G28 |
| prop:bound | IQDifferenceAlgebra.iq_range_pair_square_bound | Show bound for actual max/min, sum over distinct pairs, and integrate with Cauchy–Schwarz. | G01 G26 |
| prop:sensitivity | Finite range algebra only | Nested iid range coupling, positive expected range, monotonicity in k and rho with endpoint, linear scaling. | G26 |
| prop:conditional | IQDifferenceAlgebra.iq_conditional_example, iq_conditional_variance_example | Gaussian regression with regular conditional version and shifted folded-normal expectation. | G03 G04 G25 |
| prop:average | EquicorrelationVectors; projection algebra | Measurable functions of independent Gaussian orthogonal projections; singular endpoints. | G02 G26 |
| prop:heterogeneous | IQDifferenceAlgebra.iq_gap_heterogeneous_variance_nonnegative | Affine contrast law, shifted folded normal and degenerate constant gap; correlation one counterexample. | G01 G02 G25 |
| prop:quantile | No matching full theorem identified | CDF continuity/strict increase, inverse quantile and probability interval interpretation. | G14 G25 |
| prop:selection | Conditional algebra only | Event conditioning of signed gap, truncated normal first moment, positive denominator. | G03 G06 G14 G29 |
| prop:second | IQDifferenceAlgebra.iq_range_pair_square_bound | Joint min/max density by product-law integration, second moment formula and integrability. | G26 G30 |

## analyses/iq-test-differences/iq_test_differences.tex

355 lines. Review complete mathematical and prose content.

### prop:moments: Moment identities ([47–52](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L47-L52))

&#92;label{prop:moments} If two scores have finite second moments, common mean and common variance $&#92;sigma^2&gt;0$, and correlation $&#92;rho$, then $&#92;E D=0$, $&#92;E D^2=2&#92;sigma^2(1-&#92;rho)$ and $&#92;E A&#92;le &#92;sigma&#92;sqrt{2(1-&#92;rho)}$.

Proof mapping: G01; IQDifferenceAlgebra.iq_gap_variance; FiniteMoments; General L2 expectation/covariance and Cauchy–Schwarz, not merely scalar identity.. **Full-scope acceptance pending.**
### prop:domain: Admissible equicorrelation ([58–67](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L58-L67))

&#92;label{prop:domain} The matrix $C=(1-&#92;rho)I_k+&#92;rho&#92;one&#92;one^&#92;T$ is positive semidefinite exactly when $-1/(k-1)&#92;le&#92;rho&#92;le1$. For iid standard normals $Z_j$, with $&#92;bar Z=k^{-1}&#92;sum_j Z_j$, the vector &#92;[ X_j=&#92;mu+&#92;sigma&#92;{&#92;sqrt{1-&#92;rho}(Z_j-&#92;bar Z) +&#92;sqrt{1+(k-1)&#92;rho}&#92;,&#92;bar Z&#92;} &#92;] has the Gaussian law with covariance $&#92;sigma^2C$.

Proof mapping: G02; EquicorrelationVectors; IQDifferenceAlgebra.iq_equicorrelation_domain; PSD iff and actual iid-normal projection construction including singular endpoints.. **Full-scope acceptance pending.**
### prop:gap: Absolute two-score gap ([79–88](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L79-L88))

&#92;label{prop:gap} Under joint normality, let $&#92;tau^2=2&#92;sigma^2(1-&#92;rho)$. For $&#92;tau&gt;0$ and $a&#92;ge0$, &#92;[ &#92;E A=&#92;tau&#92;sqrt{2/&#92;pi},&#92;quad &#92;mathbb{P}(A&#92;le a)=2&#92;Phi(a/&#92;tau)-1,&#92;quad &#92;Var(A)=&#92;tau^2(1-2/&#92;pi). &#92;] For $&#92;tau=0$ the gap vanishes almost surely.

Proof mapping: G02 G14 G25; IQDifferenceAlgebra.iq_gap_variance; Normal contrast law, half-normal CDF/first and second moments; zero-variance a.s.. **Full-scope acceptance pending.**
### prop:range: Range distribution and expectation ([101–111](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L101-L111))

&#92;label{prop:range} Put $s=&#92;sigma&#92;sqrt{1-&#92;rho}$ and let $M_k=&#92;max_j Z_j$. Then &#92;[ &#92;E R_k=2s&#92;,a_k,&#92;qquad a_k=k&#92;int_{&#92;mathbb R}z&#92;phi(z)&#92;Phi(z)^{k-1}&#92;,dz. &#92;] For $s&gt;0$ and $r&#92;ge0$, &#92;[ &#92;mathbb{P}(R_k&#92;le r)=k&#92;int_{&#92;mathbb R}&#92;phi(z) [&#92;Phi(z+r/s)-&#92;Phi(z)]^{k-1}&#92;,dz. &#92;]

Proof mapping: G02 G14 G26; IQDifferenceAlgebra.iq_absolute_shift, iq_absolute_scale; Measurable extrema, iid maximum law, unique minimum a.s., range CDF and expectation integral.. **Full-scope acceptance pending.**
### prop:five: Five-test closed form ([123–128](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L123-L128))

&#92;label{prop:five} &#92;[ a_5=&#92;frac5{4&#92;sqrt{&#92;pi}} &#92;left(1+&#92;frac6&#92;pi&#92;arcsin(1/3)&#92;right). &#92;]

Proof mapping: G26 G27; No matching full theorem identified; Integration by parts, density rescaling, three-way Gaussian orthant identity and exact a5.. **Full-scope acceptance pending.**
### prop:mixtures: Same marginal normals, different gaps ([146–154](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L146-L154))

&#92;label{prop:mixtures} Fix $k&#92;ge2$ and $&#92;sigma&gt;0$. Let a random admissible correlation $C$ select a conditional Gaussian equicorrelation model with fixed $&#92;mu,&#92;sigma$ and $&#92;E C=&#92;rho$. The unconditional marginal laws are normal, and each pair has correlation $&#92;rho$. The absolute gap and range means equal respectively $2&#92;sigma&#92;E&#92;sqrt{1-C}/&#92;sqrt&#92;pi$ and $2&#92;sigma a_k&#92;E&#92;sqrt{1-C}$. Unless $C$ is constant these are strictly smaller than the corresponding single Gaussian answers.

Proof mapping: G01 G05 G06 G25 G26 G28; IQDifferenceAlgebra.iq_weighted_scale_jensen_deficit, iq_weighted_scale_jensen_strict, iq_shared_mixture_average, iq_smooth_mixture_average; General mixture kernel, unchanged normal margins, total covariance and strict Jensen for nonconstant mixing.. **Full-scope acceptance pending.**
### prop:block: Average correlation is insufficient ([174–179](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L174-L179))

&#92;label{prop:block} Take a jointly normal pair $(U,V)$ and form three copies of $U$ and two copies of $V$, with common mean and SD $&#92;sigma$ and correlation $1/3$. Their average pairwise correlation is 0.6, but their expected range is $2&#92;sigma&#92;sqrt{(2/3)/&#92;pi}$.

Proof mapping: G25 G28; IQDifferenceAlgebra.iq_block_average; Actual replicated Gaussian pair law, range and pair-average distinction.. **Full-scope acceptance pending.**
### prop:bound: Moment-only range bound ([187–190](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L187-L190))

&#92;label{prop:bound} For equal means, equal variances and common correlation, $&#92;E R_k&#92;le&#92;sigma&#92;sqrt{k(k-1)(1-&#92;rho)}$.

Proof mapping: G01 G26; IQDifferenceAlgebra.iq_range_pair_square_bound; Show bound for actual max/min, sum over distinct pairs, and integrate with Cauchy–Schwarz.. **Full-scope acceptance pending.**
### prop:sensitivity: Sensitivity ([197–201](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L197-L201))

&#92;label{prop:sensitivity} For fixed admissible correlation, $&#92;E R_k$ is nondecreasing with $k$ over admissible dimensions. For fixed $k$ it decreases with $&#92;rho$, strictly before $&#92;rho=1$, and scales linearly in $&#92;sigma$.

Proof mapping: G26; Finite range algebra only; Nested iid range coupling, positive expected range, monotonicity in k and rho with endpoint, linear scaling.. **Full-scope acceptance pending.**
### prop:conditional: Observed first score ([209–216](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L209-L216))

&#92;label{prop:conditional} For $&#124;&#92;rho&#124;&lt;1$, given $X_1=x$ in the Gaussian two-test model, $D$ is normal with mean $d=(1-&#92;rho)(x-&#92;mu)$ and SD $t=&#92;sigma&#92;sqrt{1-&#92;rho^2}$. Its conditional absolute mean is &#92;[ 2t&#92;phi(d/t)+d[2&#92;Phi(d/t)-1]. &#92;]

Proof mapping: G03 G04 G25; IQDifferenceAlgebra.iq_conditional_example, iq_conditional_variance_example; Gaussian regression with regular conditional version and shifted folded-normal expectation.. **Full-scope acceptance pending.**
### prop:average: Range independent of battery average ([228–230](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L228-L230))

&#92;label{prop:average} Under the Gaussian equicorrelation model, $R_k$ and $&#92;bar X$ are independent, including the degenerate boundaries.

Proof mapping: G02 G26; EquicorrelationVectors; projection algebra; Measurable functions of independent Gaussian orthogonal projections; singular endpoints.. **Full-scope acceptance pending.**
### prop:heterogeneous: Heterogeneous scores ([239–250](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L239-L250))

&#92;label{prop:heterogeneous} Let $(X,Y)$ be jointly normal with means $&#92;mu_X,&#92;mu_Y$, positive SDs $&#92;sigma_X,&#92;sigma_Y$ and correlation $&#92;rho$. Write $&#92;delta=&#92;mu_X-&#92;mu_Y$ and $v=&#92;sigma_X^2+&#92;sigma_Y^2-2&#92;rho&#92;sigma_X&#92;sigma_Y$. Then $X-Y&#92;sim N(&#92;delta,v)$, and for $v&gt;0$ &#92;[ &#92;E&#124;X-Y&#124;=2&#92;sqrt v&#92;,&#92;phi(&#92;delta/&#92;sqrt v) +&#92;delta[2&#92;Phi(&#92;delta/&#92;sqrt v)-1]. &#92;] At $v=0$ the absolute difference is $&#124;&#92;delta&#124;$ almost surely.

Proof mapping: G01 G02 G25; IQDifferenceAlgebra.iq_gap_heterogeneous_variance_nonnegative; Affine contrast law, shifted folded normal and degenerate constant gap; correlation one counterexample.. **Full-scope acceptance pending.**
### prop:quantile: Quantiles of the equal-mean gap ([259–262](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L259-L262))

&#92;label{prop:quantile} When $&#92;tau&gt;0$ is the SD of the Gaussian contrast and $0&lt;p&lt;1$, its absolute-gap $p$-quantile is $&#92;tau&#92;Phi^{-1}((1+p)/2)$.

Proof mapping: G14 G25; No matching full theorem identified; CDF continuity/strict increase, inverse quantile and probability interval interpretation.. **Full-scope acceptance pending.**
### prop:selection: Threshold selection ([272–279](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L272-L279))

&#92;label{prop:selection} In the Gaussian two-test model with $&#92;sigma&gt;0$, $&#124;&#92;rho&#124;&lt;1$ and finite threshold $c$, put $z=(c-&#92;mu)/&#92;sigma$. Then &#92;[ &#92;E[D&#92;mid X_1&gt;c]=(1-&#92;rho)&#92;sigma &#92;frac{&#92;phi(z)}{1-&#92;Phi(z)}. &#92;]

Proof mapping: G03 G06 G14 G29; Conditional algebra only; Event conditioning of signed gap, truncated normal first moment, positive denominator.. **Full-scope acceptance pending.**
### prop:second: Joint extremes ([291–303](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L291-L303))

&#92;label{prop:second} For $k&#92;ge2$ iid standard normals, the minimum $m_k$ and maximum $M_k$ have joint density &#92;[ k(k-1)&#92;phi(u)&#92;phi(v)[&#92;Phi(v)-&#92;Phi(u)]^{k-2},&#92;qquad u&lt;v. &#92;] Consequently, for $s=&#92;sigma&#92;sqrt{1-&#92;rho}$, &#92;[ &#92;E R_k^2=s^2 k(k-1) &#92;int_{-&#92;infty}^&#92;infty&#92;int_u^&#92;infty (v-u)^2&#92;phi(u)&#92;phi(v)[&#92;Phi(v)-&#92;Phi(u)]^{k-2}&#92;,dv&#92;,du. &#92;]

Proof mapping: G26 G30; IQDifferenceAlgebra.iq_range_pair_square_bound; Joint min/max density by product-law integration, second moment formula and integrability.. **Full-scope acceptance pending.**

| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [3–36](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L3-L36) | span | &#92;input{../../library/latex/report_style} &#92;title{Differences and Ranges of IQ Scores} &#92;subtitle{Independent individuals, correlated tests, and conditional discre |
| [37–45](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L37-L45) | span | &#92;chapter{Model, estimands and assumptions} The upstream analyses are &#92;citep{iqsource,simsource}. Let $X_j$ denote test $j$ for one person, or let $X_1,X_2$ deno |
| [47](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L47) | label | prop:moments |
| [47–56](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L47-L56) | span | &#92;begin{proposition}[Moment identities]&#92;label{prop:moments} If two scores have finite second moments, common mean and common variance $&#92;sigma^2&gt;0$, and correlati |
| [58](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L58) | label | prop:domain |
| [58–76](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L58-L76) | span | &#92;begin{proposition}[Admissible equicorrelation]&#92;label{prop:domain} The matrix $C=(1-&#92;rho)I_k+&#92;rho&#92;one&#92;one^&#92;T$ is positive semidefinite exactly when $-1/(k-1)&#92;le |
| [62–65](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L62-L65) | display | &#92;[ X_j=&#92;mu+&#92;sigma&#92;{&#92;sqrt{1-&#92;rho}(Z_j-&#92;bar Z) +&#92;sqrt{1+(k-1)&#92;rho}&#92;,&#92;bar Z&#92;} &#92;] |
| [77](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L77) | span | &#92;chapter{Exact Gaussian differences and ranges} |
| [79](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L79) | label | prop:gap |
| [79–99](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L79-L99) | span | &#92;begin{proposition}[Absolute two-score gap]&#92;label{prop:gap} Under joint normality, let $&#92;tau^2=2&#92;sigma^2(1-&#92;rho)$. For $&#92;tau&gt;0$ and $a&#92;ge0$, &#92;[ &#92;E A=&#92;tau&#92;sqrt{2 |
| [82–86](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L82-L86) | display | &#92;[ &#92;E A=&#92;tau&#92;sqrt{2/&#92;pi},&#92;quad &#92;mathbb{P}(A&#92;le a)=2&#92;Phi(a/&#92;tau)-1,&#92;quad &#92;Var(A)=&#92;tau^2(1-2/&#92;pi). &#92;] |
| [101](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L101) | label | prop:range |
| [101–121](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L101-L121) | span | &#92;begin{proposition}[Range distribution and expectation]&#92;label{prop:range} Put $s=&#92;sigma&#92;sqrt{1-&#92;rho}$ and let $M_k=&#92;max_j Z_j$. Then &#92;[ &#92;E R_k=2s&#92;,a_k,&#92;qquad a_ |
| [103–105](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L103-L105) | display | &#92;[ &#92;E R_k=2s&#92;,a_k,&#92;qquad a_k=k&#92;int_{&#92;mathbb R}z&#92;phi(z)&#92;Phi(z)^{k-1}&#92;,dz. &#92;] |
| [107–110](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L107-L110) | display | &#92;[ &#92;mathbb{P}(R_k&#92;le r)=k&#92;int_{&#92;mathbb R}&#92;phi(z) [&#92;Phi(z+r/s)-&#92;Phi(z)]^{k-1}&#92;,dz. &#92;] |
| [123](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L123) | label | prop:five |
| [123–143](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L123-L143) | span | &#92;begin{proposition}[Five-test closed form]&#92;label{prop:five} &#92;[ a_5=&#92;frac5{4&#92;sqrt{&#92;pi}} &#92;left(1+&#92;frac6&#92;pi&#92;arcsin(1/3)&#92;right). &#92;] &#92;end{proposition} &#92;begin{proof} |
| [124–127](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L124-L127) | display | &#92;[ a_5=&#92;frac5{4&#92;sqrt{&#92;pi}} &#92;left(1+&#92;frac6&#92;pi&#92;arcsin(1/3)&#92;right). &#92;] |
| [144](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L144) | span | &#92;chapter{Identification failures and sensitivity} |
| [146](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L146) | label | prop:mixtures |
| [146–172](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L146-L172) | span | &#92;begin{proposition}[Same marginal normals, different gaps]&#92;label{prop:mixtures} Fix $k&#92;ge2$ and $&#92;sigma&gt;0$. Let a random admissible correlation $C$ select a con |
| [162–164](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L162-L164) | display | &#92;[ wa^2+(1-w)b^2-(wa+(1-w)b)^2=w(1-w)(a-b)^2. &#92;] |
| [174](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L174) | label | prop:block |
| [174–185](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L174-L185) | span | &#92;begin{proposition}[Average correlation is insufficient]&#92;label{prop:block} Take a jointly normal pair $(U,V)$ and form three copies of $U$ and two copies of $V$ |
| [187](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L187) | label | prop:bound |
| [187–195](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L187-L195) | span | &#92;begin{proposition}[Moment-only range bound]&#92;label{prop:bound} For equal means, equal variances and common correlation, $&#92;E R_k&#92;le&#92;sigma&#92;sqrt{k(k-1)(1-&#92;rho)}$. |
| [197](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L197) | label | prop:sensitivity |
| [197–206](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L197-L206) | span | &#92;begin{proposition}[Sensitivity]&#92;label{prop:sensitivity} For fixed admissible correlation, $&#92;E R_k$ is nondecreasing with $k$ over admissible dimensions. For fi |
| [207](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L207) | span | &#92;chapter{Conditioning versus unconditional comparison} |
| [209](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L209) | label | prop:conditional |
| [209–226](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L209-L226) | span | &#92;begin{proposition}[Observed first score]&#92;label{prop:conditional} For $&#124;&#92;rho&#124;&lt;1$, given $X_1=x$ in the Gaussian two-test model, $D$ is normal with mean $d=(1-&#92;r |
| [213–215](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L213-L215) | display | &#92;[ 2t&#92;phi(d/t)+d[2&#92;Phi(d/t)-1]. &#92;] |
| [228](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L228) | label | prop:average |
| [228–236](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L228-L236) | span | &#92;begin{proposition}[Range independent of battery average]&#92;label{prop:average} Under the Gaussian equicorrelation model, $R_k$ and $&#92;bar X$ are independent, incl |
| [238–268](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L238-L268) | span | &#92;section{Unequal scales, means, and individual uncertainty} &#92;begin{proposition}[Heterogeneous scores]&#92;label{prop:heterogeneous} Let $(X,Y)$ be jointly normal wi |
| [239](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L239) | label | prop:heterogeneous |
| [245–248](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L245-L248) | display | &#92;[ &#92;E&#124;X-Y&#124;=2&#92;sqrt v&#92;,&#92;phi(&#92;delta/&#92;sqrt v) +&#92;delta[2&#92;Phi(&#92;delta/&#92;sqrt v)-1]. &#92;] |
| [259](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L259) | label | prop:quantile |
| [271–287](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L271-L287) | span | &#92;section{Selection on a high first score} &#92;begin{proposition}[Threshold selection]&#92;label{prop:selection} In the Gaussian two-test model with $&#92;sigma&gt;0$, $&#124;&#92;rho&#124; |
| [272](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L272) | label | prop:selection |
| [275–278](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L275-L278) | display | &#92;[ &#92;E[D&#92;mid X_1&gt;c]=(1-&#92;rho)&#92;sigma &#92;frac{&#92;phi(z)}{1-&#92;Phi(z)}. &#92;] |
| [290–313](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L290-L313) | span | &#92;section{Second moment of the range} &#92;begin{proposition}[Joint extremes]&#92;label{prop:second} For $k&#92;ge2$ iid standard normals, the minimum $m_k$ and maximum $M_k |
| [291](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L291) | label | prop:second |
| [294–296](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L294-L296) | display | &#92;[ k(k-1)&#92;phi(u)&#92;phi(v)[&#92;Phi(v)-&#92;Phi(u)]^{k-2},&#92;qquad u&lt;v. &#92;] |
| [298–302](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L298-L302) | display | &#92;[ &#92;E R_k^2=s^2 k(k-1) &#92;int_{-&#92;infty}^&#92;infty&#92;int_u^&#92;infty (v-u)^2&#92;phi(u)&#92;phi(v)[&#92;Phi(v)-&#92;Phi(u)]^{k-2}&#92;,dv&#92;,du. &#92;] |
| [314–328](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L314-L328) | span | &#92;chapter{Scope and verification} Normality, equal scales and common correlations are assumptions, not empirical findings. Real tests may have ceiling effects, r |
| [329–354](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_test_differences.tex#L329-L354) | span | &#92;chapter{Proof register} The Rocq source includes deterministic affine contrast, finite pairwise-square bound, heterogeneous variance, two-component scale inequ |

## analyses/iq-test-differences/iq_difference_simulations.tex

140 lines. Review complete mathematical and prose content.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [3](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L3) | span | &#92;input{../../library/latex/simulation_style} |
| [6–54](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L6-L54) | span | &#92;usepackage{catchfile} &#92;newcommand{&#92;IQResultsTable}[1]{% &#92;CatchFileDef{&#92;IQResultRows}{#1}{}% &#92;begin{center} &#92;small&#92;setlength{&#92;tabcolsep}{2pt} &#92;begin{tab |
| [55–67](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L55-L67) | span | &#92;chapter{Experimental design} Each row represents one synthetic battery or one independent pair of people. The default campaign comprises eight replicates of fi |
| [68–83](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L68-L83) | span | &#92;chapter{Uncertainty and acceptance} For iid rows with finite second moment, the unbiased sample variance is $S^2=&#92;sum_i(y_i-&#92;bar y)^2/(n-1)$ by expanding squar |
| [74](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L74) | display | &#92;[M_2=M_{2,a}+M_{2,b}+&#92;frac{n_a n_b}{n_a+n_b}(m_b-m_a)^2.&#92;] |
| [84](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L84) | span | &#92;chapter{Recorded results} |
| [85–99](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L85-L99) | span | &#92;section{Dask campaign status} &#92;IfFileExists{simulation-data/results.tex}{% &#92;input{simulation-data/run.tex} &#92;IQResultsTable{simulation-data/results.tex} }{&#92;text |
| [100–109](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L100-L109) | span | &#92;section{Separately executed offline numerical check} &#92;input{offline-validation/run.tex} &#92;IQResultsTable{offline-validation/results.tex} The offline check used |
| [110–134](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L110-L134) | span | &#92;chapter{Reproducibility and contract scope} The new source reuses the shared provenance functions, isolates smoke results from production data, and guards near |
| [135–139](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/iq_difference_simulations.tex#L135-L139) | span | &#92;chapter{Implementation} &#92;lstinputlisting[language=Python]{simulate.py} &#92;ProjectReportAIAppendix &#92;paragraph{This analysis specifically.} ChatGPT (GPT-6.2) prepa |

## analyses/iq-test-differences/simulation-data/results.tex

11 lines. Numerical/provenance input; separate analytic targets from observed values.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [1–10](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/simulation-data/results.tex#L1-L10) | span | Independent people & 16.92617 & 16.92569 & 0.00202 & 16.92617 & 16.92569 & 0.00202 & PASS &#92;&#92; Two tests & 10.70538 & 10.70474 & 0.00128 & 10.70538 & 10.70474 & 0 |

## analyses/iq-test-differences/simulation-data/run.tex

2 lines. Numerical/provenance input; separate analytic targets from observed values.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [1](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/simulation-data/run.tex#L1) | span | Executed 40,000,000 rows per scenario in 8 replicates; block size 250,000, root seed 20261126, 4 threads. |

## analyses/iq-test-differences/offline-validation/results.tex

11 lines. Numerical/provenance input; separate analytic targets from observed values.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [1–10](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/offline-validation/results.tex#L1-L10) | span | Independent people & 16.92617 & 16.92569 & 0.00202 & 16.92617 & 16.92569 & 0.00202 & PASS &#92;&#92; Two tests & 10.70538 & 10.70474 & 0.00128 & 10.70538 & 10.70474 & 0 |

## analyses/iq-test-differences/offline-validation/run.tex

9 lines. Numerical/provenance input; separate analytic targets from observed values.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [1–8](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/analyses/iq-test-differences/offline-validation/run.tex#L1-L8) | span | Offline numerical-kernel check: 40,000,000 rows per scenario, eight replicates, 250,000 rows per block, seed 20261126, four threads. All ten scenarios and 1,600 |

## Simulation companion: unlabelled mathematical obligations

- Highlights/design: independent-person and same-person gaps, RMS, five-test range, conditional gap, projection and singular negative endpoint, mixture and block laws (G02–G04, G25–G28).
- Uncertainty: unbiased sample variance under iid finite-second-moment assumptions; pooled centered SS; variance of sample mean; estimated SE (not necessarily unbiased); six-SE engineering criterion and degenerate zero variance (G01, G07, G12–G13).
- Recorded results: rigorous analytic reference enclosures for ten cases and three estimands; acceptance arithmetic for retained inputs and explicit tolerance (G18, G24–G30).
- Implementation: block counts/partition, reducer mathematical equivalence, finite precision and source-to-specification correspondence. PRNG independence is not a proved fact about a deterministic algorithm.

## Counts and boundary

6 files; 15 formal environments, 12 display anchors, 15 labels, 34 source spans. Syntactic counts, not theorem counts or completion percentages. Exact semantic classification, kernel matching and assumption audit remain open.

## Complete AI disclosure

ChatGPT assisted source retrieval, indexing, mathematical classification and comparison against existing named proofs. No new mathematical verification, PDF validation, empirical validation or certified numerical bound is claimed.
