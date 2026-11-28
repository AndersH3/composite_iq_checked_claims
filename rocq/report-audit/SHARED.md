# Shared report foundations, statistics and templates

**AI disclosure:** AI-assisted obligation-discovery index for Anders Hellström, baseline `e790af0559c716596d2d251af32057879689672c`. Shared statements are counted once. Historical mappings are leads, not full-scope verification. Source-span and equation anchors overlap intentionally. Nonmathematical presentation and disclosure spans are retained for classification.

## reporting/proof_foundations.tex

220 lines. Review mathematical content and distinguish presentation support.

### pf:moments: Finite moments and affine changes of scale ([29–40](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L29-L40))

&#92;label{pf:moments} Let a real random vector &#92;(X&#92;) have finite second moments, mean &#92;(&#92;mu&#92;) and covariance &#92;(&#92;Sigma&#92;). Let &#92;(Y&#92;) be square-integrable, &#92;(w&#92;) a deterministic vector of matching dimension, and &#92;(b,s&#92;) real constants. Then &#92;[ &#92;E(w^{&#92;mathsf T}X)=w^{&#92;mathsf T}&#92;mu,&#92;qquad &#92;Var(w^{&#92;mathsf T}X)=w^{&#92;mathsf T}&#92;Sigma w,&#92;qquad &#92;SD(b+sY)=&#124;s&#124;&#92;SD(Y). &#92;] A zero variance is equivalent to equality with the mean almost surely.

Historical mapping: Finite moments and affine changes of scale; **F**; FiniteMoments weighted covariance and affine identities; finite zero-support result; 'G01'.  **Full-scope acceptance pending.**
### pf:spectral: Covariance feasibility and Gaussian construction ([60–67](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L60-L67))

&#92;label{pf:spectral} A real symmetric matrix is a covariance matrix if and only if it is positive semidefinite. For the equicorrelation matrix &#92;(R_n=(1-c)I_n+c&#92;mathbf1_n&#92;mathbf1_n^{&#92;mathsf T}&#92;), &#92;(n&#92;geq2&#92;), this is equivalent to &#92;(-1/(n-1)&#92;leq c&#92;leq1&#92;). Positive definiteness requires both inequalities to be strict.

Historical mapping: Covariance feasibility and Gaussian construction; **A**; EquicorrelationVectors finite PSD/PD characterization only; 'G02'.  **Full-scope acceptance pending.**
### pf:gaussian: Gaussian closure and block independence ([88–94](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L88-L94))

&#92;label{pf:gaussian} An affine image of a jointly Gaussian vector is jointly Gaussian. Its law is determined by its mean and covariance. Two blocks of a jointly Gaussian vector are independent whenever their cross-covariance is zero, including singular Gaussian vectors.

Historical mapping: Gaussian closure and block independence; **P**; No Gaussian probability-space construction; 'G02'.  **Full-scope acceptance pending.**
### pf:conditioning: Gaussian conditional distribution, including exact histories ([112–123](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L112-L123))

&#92;label{pf:conditioning} Suppose &#92;((U,V)&#92;) is jointly Gaussian with mean &#92;((&#92;mu_U,&#92;mu_V)&#92;), covariance blocks &#92;(A,B&#92;) and &#92;(C=&#92;Cov(U,V)&#92;), and &#92;(B&#92;) positive definite. A version of the conditional law, for every &#92;(v&#92;), is Gaussian with mean and covariance &#92;[ &#92;mu_U+CB^{-1}(v-&#92;mu_V),&#92;qquad A-CB^{-1}C^{&#92;mathsf T}. &#92;] The conditional-mean formula is the unique continuous version on the whole conditioning space. The full joint covariance need not be invertible.

Historical mapping: Gaussian conditional distribution and exact histories; **P**; TwoObservationSchur/EquicorrelationInverseVectors check algebra, not Gaussian kernels; 'G03', 'G04'.  **Full-scope acceptance pending.**
### pf:normal-marginals: Normal marginal distributions do not imply joint normality ([148–152](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L148-L152))

&#92;label{pf:normal-marginals} Normal marginals and a specified Pearson correlation do not in general determine Gaussian composite or joint-tail laws.

Historical mapping: Normal marginals do not imply joint normality; **P**; ReportCounterexample supplies a different finite discrete witness; 'G05'.  **Full-scope acceptance pending.**
### pf:events: Event arithmetic and conditional denominators ([170–179](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L170-L179))

&#92;label{pf:events} For events &#92;(A,B&#92;) with probabilities &#92;(p_A,p_B&#92;) and intersection &#92;(J&#92;), their union has probability &#92;(p_A+p_B-J&#92;). If its conditioning probability is positive, &#92;(P(B&#92;mid A)=J/p_A&#92;). The correlation of the nonconstant indicators is &#92;[ &#92;frac{J-p_Ap_B}{&#92;sqrt{p_A(1-p_A)p_B(1-p_B)}}. &#92;]

Historical mapping: Event arithmetic, ratios and indicator phi; **F**; FiniteUnion; Admissions; FiniteBridge under finite normalization and positive denominators; 'G06'.  **Full-scope acceptance pending.**
### pf:expectation: Tower property and population--conditional variance ([194–202](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L194-L202))

&#92;label{pf:expectation} For square-integrable &#92;(Y&#92;) and a sub-&#92;(&#92;sigma&#92;)-algebra &#92;(&#92;mathcal G&#92;), &#92;[ &#92;E&#92;E[Y&#92;mid&#92;mathcal G]=&#92;E Y,&#92;qquad &#92;Var(Y)=&#92;E&#92;Var(Y&#92;mid&#92;mathcal G) +&#92;Var(&#92;E[Y&#92;mid&#92;mathcal G]). &#92;]

Historical mapping: Tower property and population-conditional variance; **A**; FiniteTwoCellProjection, FiniteNestedProjection, FiniteConditionalResidual only; 'G06'. FormalML ConditionalExpectation.v now compiles; exact tower, pull-out and total variance statements still need report-level instantiation. **Full-scope acceptance pending.**

| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [1–2](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L1-L2) | span | &#92;chapter{Referenced foundations and full working proofs} &#92;label{sec:proof-foundations} |
| [2](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L2) | label | sec:proof-foundations |
| [4–13](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L4-L13) | span | The results below supply the mathematical foundations used in this report. The explicitly assumed inputs are finite second moments and, where stated, a jointly |
| [15–27](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L15-L27) | span | &#92;noindent&#92;textbf{Current Python/Dask reproducibility boundary.} The numerical experiment is documented in &#92;path{reporting/run.json}, the shared Python/Dask/Deal |
| [29–58](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L29-L58) | span | &#92;begin{proposition}[Finite moments and affine changes of scale] &#92;label{pf:moments} Let a real random vector &#92;(X&#92;) have finite second moments, mean &#92;(&#92;mu&#92;) and c |
| [30](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L30) | label | pf:moments — Finite moments and affine changes of scale; **F**; FiniteMoments weighted covariance and affine identities; finite zero-support result; 'G01' |
| [34–38](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L34-L38) | display | &#92;[ &#92;E(w^{&#92;mathsf T}X)=w^{&#92;mathsf T}&#92;mu,&#92;qquad &#92;Var(w^{&#92;mathsf T}X)=w^{&#92;mathsf T}&#92;Sigma w,&#92;qquad &#92;SD(b+sY)=&#124;s&#124;&#92;SD(Y). &#92;] |
| [45–49](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L45-L49) | display | &#92;[ &#92;E&#92;!&#92;left[&#92;Big(&#92;sum_iw_i(X_i-&#92;mu_i)&#92;Big)^2&#92;right] =&#92;sum_{i,j}w_iw_j&#92;E[(X_i-&#92;mu_i)(X_j-&#92;mu_j)] =w^{&#92;mathsf T}&#92;Sigma w. &#92;] |
| [60–86](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L60-L86) | span | &#92;begin{proposition}[Covariance feasibility and Gaussian construction] &#92;label{pf:spectral} A real symmetric matrix is a covariance matrix if and only if it is po |
| [61](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L61) | label | pf:spectral — Covariance feasibility and Gaussian construction; **A**; EquicorrelationVectors finite PSD/PD characterization only; 'G02' |
| [88–110](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L88-L110) | span | &#92;begin{proposition}[Gaussian closure and block independence] &#92;label{pf:gaussian} An affine image of a jointly Gaussian vector is jointly Gaussian. Its law is de |
| [89](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L89) | label | pf:gaussian — Gaussian closure and block independence; **P**; No Gaussian probability-space construction; 'G02' |
| [112–146](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L112-L146) | span | &#92;begin{proposition}[Gaussian conditional distribution, including exact histories] &#92;label{pf:conditioning} Suppose &#92;((U,V)&#92;) is jointly Gaussian with mean &#92;((&#92;mu |
| [113](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L113) | label | pf:conditioning — Gaussian conditional distribution and exact histories; **P**; TwoObservationSchur/EquicorrelationInverseVectors check algebra, not Gaussian kernels; 'G03', 'G04' |
| [118–120](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L118-L120) | display | &#92;[ &#92;mu_U+CB^{-1}(v-&#92;mu_V),&#92;qquad A-CB^{-1}C^{&#92;mathsf T}. &#92;] |
| [132–134](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L132-L134) | display | &#92;[ P(U&#92;in H,V&#92;in D)=&#92;int_D K(v,H)P_V(dv) &#92;] |
| [148–168](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L148-L168) | span | &#92;begin{proposition}[Normal marginal distributions do not imply joint normality] &#92;label{pf:normal-marginals} Normal marginals and a specified Pearson correlation |
| [149](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L149) | label | pf:normal-marginals — Normal marginals do not imply joint normality; **P**; ReportCounterexample supplies a different finite discrete witness; 'G05' |
| [170–192](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L170-L192) | span | &#92;begin{proposition}[Event arithmetic and conditional denominators] &#92;label{pf:events} For events &#92;(A,B&#92;) with probabilities &#92;(p_A,p_B&#92;) and intersection &#92;(J&#92;), t |
| [171](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L171) | label | pf:events — Event arithmetic, ratios and indicator phi; **F**; FiniteUnion; Admissions; FiniteBridge under finite normalization and positive denominators; 'G06' |
| [176–178](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L176-L178) | display | &#92;[ &#92;frac{J-p_Ap_B}{&#92;sqrt{p_A(1-p_A)p_B(1-p_B)}}. &#92;] |
| [194–219](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L194-L219) | span | &#92;begin{proposition}[Tower property and population--conditional variance] &#92;label{pf:expectation} For square-integrable &#92;(Y&#92;) and a sub-&#92;(&#92;sigma&#92;)-algebra &#92;(&#92;math |
| [195](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L195) | label | pf:expectation — Tower property and population-conditional variance; **A**; FiniteTwoCellProjection, FiniteNestedProjection, FiniteConditionalResidual only; 'G06' |
| [197–201](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/proof_foundations.tex#L197-L201) | display | &#92;[ &#92;E&#92;E[Y&#92;mid&#92;mathcal G]=&#92;E Y,&#92;qquad &#92;Var(Y)=&#92;E&#92;Var(Y&#92;mid&#92;mathcal G) +&#92;Var(&#92;E[Y&#92;mid&#92;mathcal G]). &#92;] |

## reporting/statistical_methods.tex

240 lines. Review mathematical content and distinguish presentation support.

### sm:normal-sample: Normal sample moments and the chi-square pivot ([15–22](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L15-L22))

&#92;label{sm:normal-sample} For an integer &#92;(m&#92;geq2&#92;), independent &#92;(Y_i&#92;sim N(&#92;mu,v)&#92;), &#92;(v&gt;0&#92;), the sample mean is &#92;(N(&#92;mu,v/m)&#92;). With &#92;(S^2=&#92;sum_i(Y_i-&#92;bar Y)^2/(m-1)&#92;), &#92;((m-1)S^2/v&#92;sim&#92;chi^2_{m-1}&#92;), independently of &#92;(&#92;bar Y&#92;), and &#92;(&#92;E S^2=v&#92;).

Historical mapping: Independent Gaussian sample moments and chi-square pivot; **P**; No normal-sample or chi-square distribution theorem in current modules; 'G07'.  **Full-scope acceptance pending.**
### sm:sd-interval: SD intervals and fixed-parameter reference bands ([42–55](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L42-L55))

&#92;label{sm:sd-interval} Let &#92;(q_u&#92;) denote a &#92;(&#92;chi^2_{m-1}&#92;) quantile and &#92;(0&lt;&#92;alpha&lt;1&#92;). An exact &#92;(1-&#92;alpha&#92;) confidence interval for the unknown SD under this normal model is &#92;[ &#92;left[&#92;sqrt{&#92;frac{(m-1)S^2}{q_{1-&#92;alpha/2}}}, &#92;sqrt{&#92;frac{(m-1)S^2}{q_{&#92;alpha/2}}}&#92;right]. &#92;] For a fixed theoretical &#92;(v&#92;), a reference interval for &#92;(S^2&#92;) is instead &#92;([vq_{&#92;alpha/2}/(m-1),vq_{1-&#92;alpha/2}/(m-1)]&#92;). The reference mean discrepancy in standard-error units is &#92;((&#92;bar Y-&#92;mu)/&#92;sqrt{v/m}&#92;sim N(0,1)&#92;).

Historical mapping: SD confidence intervals and reference bands; **P**; No chi-square quantile/pivot coverage proof; 'G07'.  **Full-scope acceptance pending.**
### sm:binomial: Bernoulli counts and sampling precision ([69–75](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L69-L75))

&#92;label{sm:binomial} For an integer &#92;(m&#92;geq1&#92;) and &#92;(m&#92;) independent event indicators of common probability &#92;(p&#92;in[0,1]&#92;), the count &#92;(K&#92;) is binomial, &#92;(&#92;E K=mp&#92;), and &#92;(&#92;Var(K/m)=p(1-p)/m&#92;).

Historical mapping: Bernoulli count law, expectation and variance; **A**; Finite event mass arithmetic; independent-trial binomial law missing; 'G08'. TwoRatePrecision, StratifiedBernoulli and SamplingPrecision supply finite moment/precision algebra; independent-trial binomial distribution remains open. **Full-scope acceptance pending.**
### sm:wilson: Wilson score endpoints and their coverage scope ([86–98](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L86-L98))

&#92;label{sm:wilson} For an integer &#92;(m&#92;geq1&#92;), an observed count &#92;(K&#92;in&#92;{0,&#92;ldots,m&#92;}&#92;), &#92;(0&lt;&#92;alpha&lt;1&#92;), &#92;(&#92;hat p=K/m&#92;) and &#92;(z=&#92;Phi^{-1}(1-&#92;alpha/2)&#92;), inversion of the normal score inequality gives endpoints &#92;[ &#92;frac{&#92;hat p+z^2/(2m)&#92; &#92;mathord&#92;pm&#92; z&#92;sqrt{&#92;hat p(1-&#92;hat p)/m+z^2/(4m^2)}}{1+z^2/m}. &#92;] The endpoint algebra is exact; nominal &#92;(1-&#92;alpha&#92;) coverage uses a normal score approximation and is not an exact finite-sample coverage theorem.

Historical mapping: Wilson score endpoints and coverage scope; **P**; No Rocq score-inequality inversion theorem; 'G09'. WilsonScoreAlgebra supplies verified inversion algebra; coverage scope requires exact report matching. **Full-scope acceptance pending.**
### sm:clopper-pearson: Exact equal-tail binomial intervals ([117–124](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L117-L124))

&#92;label{sm:clopper-pearson} For an integer &#92;(m&#92;geq1&#92;), a count &#92;(j&#92;in&#92;{0,&#92;ldots,m&#92;}&#92;), and &#92;(0&lt;&#92;alpha&lt;1&#92;), define &#92;(L(0)=0&#92;), &#92;(U(m)=1&#92;); for &#92;(j&gt;0&#92;), let &#92;(L(j)&#92;) solve &#92;(P_{L(j)}(K&#92;geq j)=&#92;alpha/2&#92;), and for &#92;(j&lt;m&#92;), let &#92;(U(j)&#92;) solve &#92;(P_{U(j)}(K&#92;leq j)=&#92;alpha/2&#92;). Then &#92;(P_p(L(K)&#92;leq p&#92;leq U(K))&#92;geq1-&#92;alpha&#92;) for every &#92;(p&#92;in[0,1]&#92;).

Historical mapping: Exact equal-tail binomial interval coverage; **P**; No exact conservative binomial-tail coverage proof; 'G10'.  **Full-scope acceptance pending.**
### sm:conditional-count: Conditional frequencies with random denominators ([151–159](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L151-L159))

&#92;label{sm:conditional-count} For independent repetitions of a four-cell event experiment, condition on &#92;(N_A=&#92;ell&gt;0&#92;) observations in event &#92;(A&#92;), where &#92;(P(A)&gt;0&#92;). The count also in &#92;(B&#92;) is then &#92;(&#92;mathrm{Binomial}(&#92;ell,P(B&#92;mid A))&#92;). Thus a binomial interval conditional on its observed denominator has its stated exact or approximate coverage scope. A zero denominator gives no defined conditional-frequency estimate.

Historical mapping: Conditional binomial given random denominator; **P**; Finite event conditioning only; no independent trial count conditioning; 'G11'.  **Full-scope acceptance pending.**
### sm:pooling: Pooling counts and moments ([178–190](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L178-L190))

&#92;label{sm:pooling} For a nonempty finite collection of groups of integer sizes &#92;(m_j&#92;geq2&#92;), means &#92;(&#92;bar Y_j&#92;) and sample variances &#92;(S_j^2&#92;), let &#92;(M=&#92;sum_jm_j&#92;) and &#92;(&#92;bar Y=M^{-1}&#92;sum_jm_j&#92;bar Y_j&#92;). The pooled sample variance satisfies &#92;[ (M-1)S^2=&#92;sum_j(m_j-1)S_j^2+&#92;sum_jm_j(&#92;bar Y_j-&#92;bar Y)^2. &#92;] Independent equal-design Bernoulli groups pool to a binomial count of size &#92;(M&#92;); independence is required for that probability law, not for the displayed algebraic identity.

Historical mapping: Pooled sample counts and variance identity; **A**; FiniteMoments variance tools only; full grouped sample identity not matched; 'G12'. ListPoolingAlgebra and PooledMomentsAlgebra supply verified finite-list identities; sample-law and implementation correspondence still need mapping. **Full-scope acceptance pending.**
### sm:multiple: Simultaneous diagnostics and rare-event precision ([205–210](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L205-L210))

&#92;label{sm:multiple} If &#92;(J&#92;) fixed diagnostics have false-alarm probabilities at most &#92;(&#92;alpha_j&#92;), the probability of any false alarm is at most &#92;(&#92;sum_{j=1}^J&#92;alpha_j&#92;), regardless of their dependence.

Historical mapping: Simultaneous diagnostic union bound; **A**; FiniteUnion arbitrary union bound, not general diagnostic probability model; 'G13'.  **Full-scope acceptance pending.**
### sm:rare: Zero counts, relative precision and sample-size scaling ([221–228](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L221-L228))

&#92;label{sm:rare} For independent Bernoulli trials, &#92;(P(K=0)=(1-p)^m&#92;). For &#92;(p&gt;0&#92;) the relative standard error of &#92;(K/m&#92;) is &#92;(&#92;sqrt{(1-p)/(mp)}&#92;); requiring it at most &#92;(&#92;epsilon&gt;0&#92;) means &#92;(m&#92;geq(1-p)/(p&#92;epsilon^2)&#92;). At fixed &#92;(p&#92;in(0,1)&#92;), multiplying &#92;(m&#92;) by four halves the standard error. Zero successes do not prove &#92;(p=0&#92;).

Historical mapping: Zero counts and rare-event precision scaling; **A**; Elementary real/event algebra; independent binomial sampling law absent; 'G08', 'G13'.  **Full-scope acceptance pending.**

| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [1–3](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L1-L3) | span | &#92;chapter{Statistical reference laws and uncertainty calculations} &#92;label{sec:shared-statistical-methods} &#92;label{sec:simulation-statistical-methods} |
| [2](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L2) | label | sec:shared-statistical-methods |
| [3](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L3) | label | sec:simulation-statistical-methods |
| [5–13](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L5-L13) | span | These results concern ideal independent observations from the stated model. They justify reference laws and interval calculations, rather than proving that fini |
| [15–40](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L15-L40) | span | &#92;begin{proposition}[Normal sample moments and the chi-square pivot] &#92;label{sm:normal-sample} For an integer &#92;(m&#92;geq2&#92;), independent &#92;(Y_i&#92;sim N(&#92;mu,v)&#92;), &#92;(v&gt;0&#92; |
| [16](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L16) | label | sm:normal-sample — Independent Gaussian sample moments and chi-square pivot; **P**; No normal-sample or chi-square distribution theorem in current modules; 'G07' |
| [32–35](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L32-L35) | display | &#92;[ &#92;frac{1}{v}&#92;sum_i(Y_i-&#92;bar Y)^2 =&#92;sum_iZ_i^2-T_1^2=&#92;sum_{j=2}^mT_j^2. &#92;] |
| [42–67](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L42-L67) | span | &#92;begin{corollary}[SD intervals and fixed-parameter reference bands] &#92;label{sm:sd-interval} Let &#92;(q_u&#92;) denote a &#92;(&#92;chi^2_{m-1}&#92;) quantile and &#92;(0&lt;&#92;alpha&lt;1&#92;). An |
| [43](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L43) | label | sm:sd-interval — SD confidence intervals and reference bands; **P**; No chi-square quantile/pivot coverage proof; 'G07' |
| [47–50](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L47-L50) | display | &#92;[ &#92;left[&#92;sqrt{&#92;frac{(m-1)S^2}{q_{1-&#92;alpha/2}}}, &#92;sqrt{&#92;frac{(m-1)S^2}{q_{&#92;alpha/2}}}&#92;right]. &#92;] |
| [69–84](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L69-L84) | span | &#92;begin{proposition}[Bernoulli counts and sampling precision] &#92;label{sm:binomial} For an integer &#92;(m&#92;geq1&#92;) and &#92;(m&#92;) independent event indicators of common prob |
| [70](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L70) | label | sm:binomial — Bernoulli count law, expectation and variance; **A**; Finite event mass arithmetic; independent-trial binomial law missing; 'G08' |
| [86–115](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L86-L115) | span | &#92;begin{proposition}[Wilson score endpoints and their coverage scope] &#92;label{sm:wilson} For an integer &#92;(m&#92;geq1&#92;), an observed count &#92;(K&#92;in&#92;{0,&#92;ldots,m&#92;}&#92;), &#92;(0&lt; |
| [87](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L87) | label | sm:wilson — Wilson score endpoints and coverage scope; **P**; No Rocq score-inequality inversion theorem; 'G09' |
| [92–95](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L92-L95) | display | &#92;[ &#92;frac{&#92;hat p+z^2/(2m)&#92; &#92;mathord&#92;pm&#92; z&#92;sqrt{&#92;hat p(1-&#92;hat p)/m+z^2/(4m^2)}}{1+z^2/m}. &#92;] |
| [101–103](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L101-L103) | display | &#92;[ (m+z^2)p^2-(2m&#92;hat p+z^2)p+m&#92;hat p^2&#92;leq0. &#92;] |
| [117–149](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L117-L149) | span | &#92;begin{proposition}[Exact equal-tail binomial intervals] &#92;label{sm:clopper-pearson} For an integer &#92;(m&#92;geq1&#92;), a count &#92;(j&#92;in&#92;{0,&#92;ldots,m&#92;}&#92;), and &#92;(0&lt;&#92;alpha&lt;1&#92; |
| [118](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L118) | label | sm:clopper-pearson — Exact equal-tail binomial interval coverage; **P**; No exact conservative binomial-tail coverage proof; 'G10' |
| [128–131](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L128-L131) | display | &#92;[ &#92;frac{d}{dp}P_p(K&#92;geq j) =m&#92;binom{m-1}{j-1}p^{j-1}(1-p)^{m-j}&gt;0&#92;quad(0&lt;p&lt;1). &#92;] |
| [151–176](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L151-L176) | span | &#92;begin{proposition}[Conditional frequencies with random denominators] &#92;label{sm:conditional-count} For independent repetitions of a four-cell event experiment, |
| [152](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L152) | label | sm:conditional-count — Conditional binomial given random denominator; **P**; Finite event conditioning only; no independent trial count conditioning; 'G11' |
| [165–169](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L165-L169) | display | &#92;[ P(N_{AB}=j,N_A=&#92;ell) =&#92;binom m&#92;ell&#92;binom&#92;ell j q^&#92;ell(1-q)^{m-&#92;ell} r^j(1-r)^{&#92;ell-j}. &#92;] |
| [178–203](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L178-L203) | span | &#92;begin{proposition}[Pooling counts and moments] &#92;label{sm:pooling} For a nonempty finite collection of groups of integer sizes &#92;(m_j&#92;geq2&#92;), means &#92;(&#92;bar Y_j&#92;) |
| [179](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L179) | label | sm:pooling — Pooled sample counts and variance identity; **A**; FiniteMoments variance tools only; full grouped sample identity not matched; 'G12' |
| [184–186](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L184-L186) | display | &#92;[ (M-1)S^2=&#92;sum_j(m_j-1)S_j^2+&#92;sum_jm_j(&#92;bar Y_j-&#92;bar Y)^2. &#92;] |
| [205–219](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L205-L219) | span | &#92;begin{proposition}[Simultaneous diagnostics and rare-event precision] &#92;label{sm:multiple} If &#92;(J&#92;) fixed diagnostics have false-alarm probabilities at most &#92;(&#92; |
| [206](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L206) | label | sm:multiple — Simultaneous diagnostic union bound; **A**; FiniteUnion arbitrary union bound, not general diagnostic probability model; 'G13' |
| [221–239](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L221-L239) | span | &#92;begin{corollary}[Zero counts, relative precision and sample-size scaling] &#92;label{sm:rare} For independent Bernoulli trials, &#92;(P(K=0)=(1-p)^m&#92;). For &#92;(p&gt;0&#92;) the |
| [222](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/statistical_methods.tex#L222) | label | sm:rare — Zero counts and rare-event precision scaling; **A**; Elementary real/event algebra; independent binomial sampling law absent; 'G08', 'G13' |

## reporting/ai_disclosure.tex

3 lines. Review mathematical content and distinguish presentation support.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [2](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/ai_disclosure.tex#L2) | span | &#92;input{../../library/latex/ai_disclosure} |

## reporting/book_style.tex

4 lines. Review mathematical content and distinguish presentation support.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [3](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/book_style.tex#L3) | span | &#92;input{../../library/latex/report_style} |

## reporting/simulation_style.tex

4 lines. Review mathematical content and distinguish presentation support.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [3](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/reporting/simulation_style.tex#L3) | span | &#92;input{../../library/latex/simulation_style} |

## library/latex/ai_disclosure.tex

57 lines. Review mathematical content and distinguish presentation support.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [2–8](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/ai_disclosure.tex#L2-L8) | span | This report and its supporting repository were substantially generated and revised with OpenAI Codex and collaborating AI agents. The session identifies Codex a |
| [10–16](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/ai_disclosure.tex#L10-L16) | span | AI contributions included interpreting the problem and historical articles; developing and reviewing derivations, counterexamples, theorem references, proofs an |
| [18–26](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/ai_disclosure.tex#L18-L26) | span | The requester Anders Hellström supplied questions and sources, clarified notation and averaging, selected example parameters, specified formats and verification |
| [28–35](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/ai_disclosure.tex#L28-L35) | span | Original authors and references remain credited. Historical articles are analysed rather than relicensed; replacement articles are AI-generated analytical recon |
| [37–47](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/ai_disclosure.tex#L37-L47) | span | Verification claims rest on retained commands, actual outputs, tool versions, source hashes and checksums. Previous disconnected implementations and their proof |
| [49–56](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/ai_disclosure.tex#L49-L56) | span | No participant data were collected and no empirical psychometric validation study was conducted. Simulations use synthetic observations under stated probability |

## library/latex/report_style.tex

149 lines. Review mathematical content and distinguish presentation support.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [5–33](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L5-L33) | span | &#92;documentclass[11pt,a4paper,oneside,open=any,parskip=half,headings=normal, numbers=noenddot,listof=totoc,bibliography=totoc]{scrbook} &#92;usepackage{iftex} &#92;Requ |
| [36–45](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L36-L45) | span | &#92;definecolor{ink}{HTML}{183B56} &#92;definecolor{teal}{HTML}{007F82} &#92;definecolor{rust}{HTML}{B75D36} &#92;definecolor{pale}{HTML}{EFF5F7} &#92;newcommand{&#92;ProjectAuthor}{A |
| [47–62](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L47-L62) | span | &#92;newcommand{&#92;ProjectReportRunningTitle}{Mathematical and computational report} &#92;newcommand{&#92;ProjectReportRunningSubtitle}{&#92;headmark} &#92;ihead{&#92;ProjectReportRunnin |
| [65–83](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L65-L83) | span | &#92;DeclareMathOperator{&#92;E}{E} &#92;DeclareMathOperator{&#92;Var}{Var} &#92;DeclareMathOperator{&#92;Cov}{Cov} &#92;DeclareMathOperator{&#92;SD}{SD} &#92;DeclareMathOperator{&#92;Corr}{Corr} &#92;new |
| [86–96](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L86-L96) | span | &#92;newtcolorbox{resultbox}[1][]{colback=pale,colframe=ink,boxrule=.7pt, arc=1mm,left=3mm,right=3mm,top=2mm,bottom=2mm,breakable,#1} &#92;newtcolorbox{disclosurebox} |
| [99–128](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L99-L128) | span | &#92;newcommand{&#92;ProjectReportType}{MATHEMATICAL AND COMPUTATIONAL REPORT} &#92;newcommand{&#92;ProjectReportHighlights}{&#92;textbf{Scope:} mathematical deductions, numerica |
| [130–140](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L130-L140) | span | Source, proof and simulation files are organized in the repository; this report specifies its own assumptions, references and verification scope. |
| [144–145](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L144-L145) | span | &#92;newcommand{&#92;ProjectReportAIAppendix}{% &#92;clearpage |
| [146](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L146) | label | sec:ai-disclosure |
| [146–148](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/report_style.tex#L146-L148) | span | &#92;chapter{AI disclosure and provenance}&#92;label{sec:ai-disclosure} &#92;input{../../library/latex/ai_disclosure}% } |

## library/latex/simulation_style.tex

13 lines. Review mathematical content and distinguish presentation support.


| Source lines | Anchor | Excerpt / existing lead |
|---|---|---|
| [3–12](https://github.com/AndersH3/composite_iq_checked_claims/blob/e790af0559c716596d2d251af32057879689672c/library/latex/simulation_style.tex#L3-L12) | span | &#92;input{../../library/latex/report_style} &#92;usepackage{pgfplots} &#92;pgfplotsset{compat=1.18,width=.92&#92;linewidth,height=6.0cm, every axis/.append style={grid=major |

## Counts and boundary

8 files; 16 formal environments, 13 display anchors, 20 labels, 40 source spans. Syntactic counts, not theorem counts or completion percentages. Exact semantic classification, kernel matching and assumption audit remain open.

## Complete AI disclosure

ChatGPT assisted source retrieval, indexing and comparison against the historical proof register. No new mathematical verification, PDF validation, empirical validation or certified numerical bound is claimed.
