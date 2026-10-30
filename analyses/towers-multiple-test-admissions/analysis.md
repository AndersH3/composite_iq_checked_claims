# Multiple-Test Admissions

Joint analysis and corrected version of two Grady Towers letters. Prepared 30 October 2026. The [XeLaTeX source](towers_admissions_analysis.tex) and [PDF](output/pdf/towers_admissions_analysis.pdf) are the authoritative typeset version.

# Joint assessment of the two sources

## Read the second letter as a retraction

The sources are *On using multiple tests for high IQ society admissions* ([Towers, n.d.](#ref-towersOriginal)) and its *Followup* ([Towers 2000](#ref-towersFollowup)), both hosted by Darryl Miyaguchi. The first is undated in the supplied page. The second identifies its underlying letter as dated 12 January 2000 and says that it was published posthumously with permission. The supplied Wayback captures are dated 9 March 2026 and 5 May 2022, respectively; these are archive dates, not the letters’ publication dates.

The follow-up expressly withdraws the earlier calculation. It should not be presented as independent support for the first letter’s dramatic conclusion. Towers’s useful qualitative point survives: accepting a pass on either of two imperfectly overlapping tests generally enlarges the eligible group relative to either test alone. The numerical examples and the interpretation of eligibility need correction.

This report examines the mathematical scenarios in those historical letters. It does not establish the admission policies, test correlations, or membership composition of any named society, either historically or today. The incomplete 1960 reference in the first letter can be identified as Zelen and Severo ([1960](#ref-zelen1960)); the calculations here were performed independently.

## The first letter’s principal numerical claims fail

Table 1 compares the first letter’s principal figures with recalculations under its intended Gaussian scenario. In the mixed case, $A$ means passing the top-2% cutoff on test $X$, and $B$ means passing the top-0.1% cutoff on a different test $Y$. All corrected entries assume population score correlation $\rho=0.7$.

| Quantity                                            |    Original | Corrected |
|:----------------------------------------------------|------------:|----------:|
| Both top-2% tests: population                       |   about 0.2 |  0.627627 |
| Either top-2% test: population                      |        3.83 |  3.372373 |
| Second top-2% pass, given first pass                |       10.27 | 31.381370 |
| Mixed case: either pass, population                 |        2.11 |  2.034141 |
| Mixed case: both pass, population                   | about 0.014 |  0.065859 |
| Mixed case: higher cutoff given lower, $P(B\mid A)$ |        0.69 |  3.292944 |
| Mixed case: lower cutoff given higher, $P(A\mid B)$ |       13.48 | 65.858880 |

Table 1. Selected claims in the original letter and corrected model results. All displayed probabilities are percentages, with the denominator specified.

One error is visible without a distributional model: the mixed-case union cannot be 2.11% when its marginal probabilities sum to only 2.10%. In general, $P(A\cup B)\leq P(A)+P(B)$. The corrected mixed-case failure rate on the lower-threshold test among higher-threshold passers is 34.1411%, rather than the original’s approximately 86%.

For the equal top-2% case, passing $X$ alone has probability 1.3724%, and passing $Y$ alone has the same probability. Passing *exactly one* therefore has probability 2.7447%. These are different quantities; wording such as “one test but not the other” should specify which is intended.

## What the follow-up fixes, and what remains

The follow-up replaces an approximation involving the phi coefficient with numerical summation of a bivariate-normal density. That is a substantial correction. Reimplementing its supplied BASIC grid closely reproduces its published joint probabilities. The remaining issues are:

- The equal-weight half-IQ-point grid samples the cutoff itself, giving approximately the boundary of a midpoint cell a quarter point below that cutoff. It does not integrate exactly from the stated continuous cutoff.

- The integer IQ cutoffs 133, 150, and 164 do not have exactly the nominal tail probabilities used as denominators in the follow-up.

- A conditional proportion among passers of one specified test is not automatically a proportion among society members, or even among all people eligible through either of two tests.

Appendix A separates those effects. The absent scale and cell-area factors in the density ratio cancel; they are not fatal normalization errors. The image of the follow-up’s double integral was also inspected, in addition to its HTML text and BASIC listing.

The follow-up recounts a top-5% example attributed to page 306 of Cattell’s *The Scientific Analysis of Personality*. Under the model used here, two such tests at $\rho=0.7$ have joint probability 1.95993%, rather than 1%. This checks Towers’s recollection as written. Cattell’s cited page was not independently inspected, so no error is attributed to Cattell himself.

# Corrected combined article: admissions through correlated tests

An admission rule and a test percentile answer different questions. A test cutoff may be exceeded by 2% of a reference population. A rule accepting either of two such cutoffs concerns the union of two sets of people, whose size depends on their overlap. Requiring both cutoffs concerns their intersection. Neither rule, by itself, identifies the people with the highest values of a perfectly measured underlying ability.

## Specify a joint model and distinguish the correlations

Let $X,Y$ denote standardized scores in the same reference population, with a bivariate-normal distribution: $$\begin{pmatrix}X\\Y\end{pmatrix}
\sim N_2\!\left[
\begin{pmatrix}0\\0\end{pmatrix},
\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}\right],
\qquad -1<\rho<1.$$ Here $\rho$ is the Pearson correlation of the continuous scores. It is not the reliability of either test and is not generally the correlation of the binary pass/fail indicators. Normal marginal distributions and a correlation alone do not establish equation (1); the joint distribution is an additional assumption, especially consequential in the tails.

For desired marginal pass probabilities $p_A,p_B$, use $$a=\Phi^{-1}(1-p_A),\qquad b=\Phi^{-1}(1-p_B),
\qquad A=\{X>a\},\quad B=\{Y>b\}.$$ The joint pass probability follows by conditioning on $X$: $$\boxed{J=P(A\cap B)=\int_a^\infty
\varphi(x)\,\overline{\Phi}\!\left(\frac{b-\rho x}{\sqrt{1-\rho^2}}\right)\,dx.}$$ Here $\varphi$ is the standard-normal density and $\overline{\Phi}=1-\Phi$ its upper-tail function. The remaining quantities are $$\begin{aligned}
P(A\cup B)&=p_A+p_B-J,\\
P(B\mid A)&=J/p_A, & P(A\mid B)&=J/p_B.
\end{aligned}$$ The denominators determine the question being answered.

For binary indicators $1_A,1_B$, the phi coefficient is $$\phi_{\mathrm{binary}}=
\frac{J-p_Ap_B}{\sqrt{p_A(1-p_A)p_B(1-p_B)}}.$$ This differs from the correlation of the underlying continuous Gaussian variables ([Ekström 2011](#ref-ekstrom2011)). For equal top-2% thresholds at $\rho=0.7$, $\phi_{\mathrm{binary}}\approx0.29981$, rather than 0.7. The follow-up attributes its earlier error to a phi/product-moment approximation. Without the first algorithm, its exact computational mistake cannot be reconstructed; substituting one correlation for the other is nevertheless unjustified.

## Two tests with the same nominal cutoff

For two top-2% cutoffs and $\rho=0.7$, equation (3) gives $$J=0.0062762740205,\qquad
P(A\cup B)=0.0337237259795.$$ Thus 0.627627% of the population passes both tests, and 3.372373% passes at least one. Among people who pass a specified first test, $$P(B\mid A)=\frac{0.0062762740205}{0.02}
\approx31.3814\%.$$ This statement concerns repeat qualification, not test reliability and not an unconditional probability of joining a society.

If eligibility instead means passing *either* of the two tests, the fraction of that eligible union passing both is $$P(A\cap B\mid A\cup B)=\frac{J}{2p-J}
\approx18.6109\%,\qquad p=0.02.$$ The 31.3814% and 18.6109% figures are both correct under the model; they use different denominators. Actual members may be a further selected subset of either group.

The same calculation at rarer equal cutoffs yields table 2. The cutoffs are exact nominal percentiles rather than rounded IQ points. IQ-style values in the table use mean 100 and standard deviation 16; they are scale conversions.

| Marginal tail on each test | $z$ cutoff | SD-16 cutoff | Both: population % | Second pass given first: % |
|:---------------------------|-----------:|-------------:|-------------------:|---------------------------:|
| 2%                         |   2.053749 |    132.85998 |           0.627627 |                  31.381370 |
| 0.1%                       |   3.090232 |    149.44372 |          0.0159589 |                  15.958919 |
| $1/33{,}000$               |   4.010439 |    164.16702 |        0.000231250 |                   7.631243 |

Table 2. Equal nominal cutoffs at $\rho=0.7$: population overlap and repeat qualification among passers of one specified test.

## A lower cutoff on one test and a higher cutoff on another

Let $p_A=0.02$ and $p_B=0.001$, still with $\rho=0.7$. The joint probability is $$J=0.0006585888039.$$ Consequently, $$\begin{aligned}
P(B\mid A)&=3.292944\%, &
P(A\mid B)&=65.858880\%,\\
P(A^c\mid B)&=34.141120\%, &
P(A\cup B)&=2.034141\%.
\end{aligned}$$ The asymmetry is expected: the higher-threshold passers are a much smaller group. These two events concern *different tests*. If both cutoffs were applied to the same score, the higher-cutoff event would be contained in the lower-cutoff event and the corresponding conditional probability would be 100%.

The result is sensitive to the assumed correlation. For these same mixed cutoffs, $P(A\mid B)$ is approximately 33.59% at $\rho=0.5$, 65.86% at 0.7, and 97.99% at 0.9. A nominal 0.7 is an illustrative parameter, not a universal empirical property of IQ tests. Population, norms, age, constructs, administration, and selection all matter.

These conditional model results cannot determine whether someone who passed a particular magazine test could join a particular society. That requires evidence about the actual instruments and the society’s accepted routes. Nor does the model establish the earlier claim about the prior memberships of most high-scoring society members.

## Eligibility size, rarity equivalents, and calibrated rules

The population fraction admitted by a rule can be expressed as a normal rarity equivalent. Under the equal top-2% example, the OR and AND fractions map to approximately 129.26 and 139.94, respectively, on an SD-16 scale: $$I_{\mathrm{rarity}}=100+16\Phi^{-1}(1-p_{\mathrm{eligible}}).$$ This only matches a selected fraction. It does not show that the rules select the same people as a single test at that cutoff, establish “super-high reliability,” or identify a particular level of latent intelligence. The first letter’s corresponding AND rarity equivalent of about 146 follows from its erroneous overlap probability.

Multiple tests do not make a 2% overall eligibility rule impossible. Within the stated model, one can choose the common cutoff $a_*$ to solve $$2\overline{\Phi}(a_*)-J(a_*,a_*;0.7)=0.02.$$ The solution is approximately $a_*=2.270055$, or 136.32088 on an SD-16 scale. Each test then has marginal pass rate approximately 1.16021%, while the two-test OR rule has overall rate 2%. This is an example of calibrating a *rule*; using more than one test is not inherently incompatible with a specified eligible fraction.

## Interpret the population model and the testing process

A useful report separates three questions: who exceeds a cutoff on one instrument; who is eligible under a specified admission procedure; and what the evidence supports about an individual’s abilities. Agreement on one does not settle the others. Score interpretations and reference populations need explicit support ([American Educational Research Association, American Psychological Association, and National Council on Measurement in Education 2014](#ref-standards2014), Standards 1.1–1.4 and 5.8–5.9).

An eligibility probability refers to the designated population before application or membership selection. Correlations measured among applicants or members need not equal the population correlation used in equation (1). Selection can change the relationship, and adjustments depend on the selection mechanism ([Sackett and Yang 2000](#ref-sackett2000)).

A procedure accepting the best result from repeated attempts also differs from a fixed two-test procedure. For $m$ pass events, independently of any Gaussian model, $$\max_i P(A_i)\leq P\!\left(\bigcup_{i=1}^{m}A_i\right)
\leq\min\!\left(1,\sum_{i=1}^{m}P(A_i)\right).$$ If attempts were independent with identical pass probability $p$, the union would be $1-(1-p)^m$. Actual retests usually require a model of dependence and administration history; practice and coaching can also change score distributions ([Hausknecht et al. 2007](#ref-hausknecht2007)). An analysis should calibrate the procedure actually used, including its attempts, stopping rule, and accepted instruments.

Towers was right to ask how multiple admission routes affect eligibility, and right to withdraw a faulty calculation. A defensible replacement states the rule, the reference population, the joint-distribution model, the thresholds, and each conditional denominator. Its conclusions remain conditional on those specifications.

# Numerical audit of the follow-up

The BASIC listing uses $\rho=0.7$, means 100, standard deviations 16, and grid nodes from $Q$ through 199 in steps of $h=0.5$, with the full-field denominator starting at 1. In mathematical notation its probability estimate is $$\widehat J_Q=
\frac{\displaystyle\sum_{x\in\{Q,Q+h,\ldots,199\}}
\sum_{y\in\{Q,Q+h,\ldots,199\}}g(x,y)}
{\displaystyle\sum_{x\in\{1,1+h,\ldots,199\}}
\sum_{y\in\{1,1+h,\ldots,199\}}g(x,y)},$$ where $g$ is proportional to the Gaussian density on the IQ-point coordinates. The full grid has $397^2=157{,}609$ nodes. A constant factor $1/(16\cdot16)$ and a cell area $h^2$ would cancel between the two sums. The corresponding absent scale factor also cancels in the displayed double-integral ratio in the follow-up.

| $Q$ |     Published grid ratio |    Reproduced grid ratio | Continuous joint probability |
|:----|-------------------------:|-------------------------:|-----------------------------:|
| 133 |             0.0064061692 |             0.0064061681 |                 0.0061136512 |
| 150 |            0.00014748463 |            0.00014748460 |                0.00013830591 |
| 164 | $2.6393845\times10^{-6}$ | $2.6393840\times10^{-6}$ |     $2.4390159\times10^{-6}$ |

Table 3. Reproduction of the follow-up’s grid estimates. Entries are probabilities, not percentages. The last column integrates from the actual continuous cutoff $Q$, on both tests.

The reproduced and published grid values agree to relative differences of about $2\times10^{-7}$, but not to every printed digit. The exact cause of those small differences is not established. They are far smaller than the difference between the grid estimate and the continuous probability at the intended cutoff.

Equal weighting at the boundary includes a full contribution from the node at $Q$. Viewed as midpoint quadrature, its first cell begins at $Q-h/2=Q-0.25$. The effective lower boundary is therefore shifted downward. The finite upper boundary and ordinary quadrature error add smaller discrepancies in these examples. If IQ scores were explicitly rounded to integers before classification, a separate rounding rule would be needed; a quarter-point grid shift cannot simply be assumed to be that rule.

For continuous scores, the actual marginal exceedance probabilities at the stated integer cutoffs are those in table 4. Dividing the continuous joint tail by its matching marginal gives a consistent conditional probability.

| Cutoff | Marginal pass rate | Both: population | Second pass given first |
|:-------|-------------------:|-----------------:|------------------------:|
| 133    |         1.95800788 |       0.61136512 |               31.223834 |
| 150    |         0.08890253 |       0.01383059 |               15.557028 |
| 164    |         0.00316712 |       0.00024390 |                7.701043 |

Table 4. Consistent continuous calculations at the follow-up’s integer SD-16 cutoffs, with $\rho=0.7$. All probability columns are percentages.

The follow-up divides its grid values by 0.02, 0.001, and 0.000030303. Those are approximations to desired nominal tails, not matching marginal tails of the specific grid or continuous integer cutoffs. Its approximately 32%, 15%, and 9% summaries consequently mix conventions. For exact nominal percentiles, use table 2; for actual continuous integer cutoffs, use table 4. Using the grid’s own marginal denominator gives approximately 31.51%, 15.74%, and 7.81%, a third, internally defined approximation.

# Reproducibility and numerical checks

The accompanying script evaluates equation (3) with adaptive one-dimensional quadrature and directly uses inverse survival functions for the thresholds. SciPy documents both its normal survival functions and its integration routine ([SciPy contributors n.d.](#ref-scipyNorm), [n.d.](#ref-scipyQuad)).

An independent integration identity supplies a cross-check: $$J(a,b;\rho)=\overline{\Phi}(a)\overline{\Phi}(b)+\int_0^\rho
\frac{\exp\!\left[-\dfrac{a^2-2tab+b^2}{2(1-t^2)}\right]}
{2\pi\sqrt{1-t^2}}\,dt.$$ This follows by integrating the Gaussian probability’s derivative with respect to its correlation, starting at independence. Checks also cover symmetry, probability bounds, the original mixed-case union violation, the binary phi coefficient, the calibrated OR threshold, and reproduction of the follow-up’s grid.

The CSV files contain unrounded model calculations to complement the rounded display tables. Run `make check` from this analysis folder; `make pdf` builds the report with XeLaTeX. Numerical consistency does not establish the empirical truth of the Gaussian assumptions or the chosen correlation.

<div id="refs" class="references csl-bib-body hanging-indent" entry-spacing="0">

<div id="ref-standards2014" class="csl-entry">

American Educational Research Association, American Psychological Association, and National Council on Measurement in Education. 2014. *Standards for Educational and Psychological Testing*. Washington, DC: American Educational Research Association. <https://www.testingstandards.net/uploads/7/6/6/4/76643089/9780935302356.pdf>.

</div>

<div id="ref-ekstrom2011" class="csl-entry">

Ekström, Joakim. 2011. “The Phi-Coefficient, the Tetrachoric Correlation Coefficient, and the Pearson–Yule Debate.” UCLA Department of Statistics. <https://escholarship.org/uc/item/7qp4604r>.

</div>

<div id="ref-hausknecht2007" class="csl-entry">

Hausknecht, John P., Jane A. Halpert, Nicole T. Di Paolo, and Meghan O. Moriarty Gerrard. 2007. “Retesting in Selection: A Meta-Analysis of Coaching and Practice Effects for Tests of Cognitive Ability.” *Journal of Applied Psychology* 92 (2): 373–85. <https://doi.org/10.1037/0021-9010.92.2.373>.

</div>

<div id="ref-sackett2000" class="csl-entry">

Sackett, Paul R., and Hyuck Yang. 2000. “Correction for Range Restriction: An Expanded Typology.” *Journal of Applied Psychology* 85 (1): 112–18. <https://doi.org/10.1037/0021-9010.85.1.112>.

</div>

<div id="ref-scipyQuad" class="csl-entry">

SciPy contributors. n.d. *Scipy.integrate.quad*. SciPy. <https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.quad.html>.

</div>

<div id="ref-scipyNorm" class="csl-entry">

———. n.d. *Scipy.stats.norm*. SciPy. <https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.norm.html>.

</div>

<div id="ref-towersFollowup" class="csl-entry">

Towers, Grady. 2000. “Followup to ‘on Using Multiple Tests for High IQ Society Admissions’.” Letter hosted by Darryl Miyaguchi; published posthumously with permission. <https://web.archive.org/web/20220505012535/http://miyaguchi.4sigma.org/gradytowers/followup.html>.

</div>

<div id="ref-towersOriginal" class="csl-entry">

———. n.d. “On Using Multiple Tests for High IQ Society Admissions.” Letter hosted by Darryl Miyaguchi. <https://web.archive.org/web/20260309223409/http://miyaguchi.4sigma.org/gradytowers/societies.html>.

</div>

<div id="ref-zelen1960" class="csl-entry">

Zelen, Marvin, and Norman C. Severo. 1960. “Graphs for Bivariate Normal Probabilities.” *Annals of Mathematical Statistics* 31 (3): 619–24. <https://doi.org/10.1214/aoms/1177705789>.

</div>

</div>
