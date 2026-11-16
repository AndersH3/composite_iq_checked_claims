# Six-volume Rocq proof-obligation register — D042x

## D048x — finite covariance constraints and remaining stochastic gaps

**AI disclosure:** OpenAI ChatGPT assisted this additional proof mapping. Neither a new Rocq algebra theorem nor the source audit constitutes independent validation of probabilistic assumptions.

The shared `SampleContrastCauchy.v` source supplies **142 new candidate proof scripts** (two generic bridges, 136 explicit four-test contrast Cauchy–Schwarz specializations and four general zero-variance/two-sided-covariance consequences). Their review is in [the dedicated source-order register](PROOF_REFACTOR_SAMPLE_CAUCHY.md). These support the finite-sample portion of `pf:moments`/G01, weighted pooling G12, Hoeflin/Ferguson standardized-score variance and multi-test composite correlations, Towers admissions composite-score feasibility, and Sequential score-history contrast feasibility. Only a valid nonnegative-weight finite sample and positive total mass are modeled; arbitrary covariance symbols are *not* thereby shown to be feasible.

Across all six volumes, no full Gaussian conditional distribution, normal-tail integral enclosure, independent Bernoulli/binomial probability law, normal-sample chi-square pivot, exact confidence interval coverage, pseudorandom-generator accuracy or empirical IQ population model has been proved by these algebraic constraints. The 136 related specializations must never be counted as independent statistical evidence. The canonical Rocq 9.2 workflow remains the formal acceptance gate.

> **AI DISCLOSURE:** This source-audit and formalization backlog were prepared with OpenAI ChatGPT assistance. A report proof, source scan or simulation is not a Rocq kernel proof. Author: **Anders Hellström**.

**Date:** November 16, 2026. **Pinned baseline:** [`5c23afcd48bd36302c0acd2bbdf75271abf06921`](https://github.com/AndersH3/composite_iq_checked_claims/commit/5c23afcd48bd36302c0acd2bbdf75271abf06921). The six authoritative XeLaTeX sources are linked from the four project/reporting READMEs. This register covers all six main/simulation volumes, their proof-bearing inputs and claim-to-evidence maps. It distinguishes the full report proposition from a previously kernel-checked **finite** or **algebraic** fragment.

## D047x — four-test covariance contractions and finite-list bridges (169 proof scripts)

**Author:** Anders Hellström. **AI disclosure:** OpenAI ChatGPT assisted statement design, polynomial expansion, proof scripting and this register. Kernel compilation at an exact source revision—not text or code generation—determines proof status.

The new shared [`FourContrastCovariance.v`](../library/rocq/FourContrastCovariance.v) has **169 explicit theorem proofs and 3 definitions**. Fourteen general matrix-bilinearity/quadratic identities and 136 exact variance/covariance evaluations of 16 meaningful score contrasts establish the symbolic contraction algebra. The remaining 19 proofs establish actual finite-list covariance linearity, four-test sample covariance and variance matrix bridges, nonnegative empirical covariance quadratic forms under nonnegative sample weights and positive mass, six applied composite-score formulas, and four-score sample mean linearity.

For the shared report proposition `pf:moments` (G01) this provides a direct **deterministic four-score finite-sample analogue** of `Var(w^T X)=w^T Sigma w` and `E(w^T X)=w^T mu`, plus the constructive positive-semidefinite sample covariance result. The D046x pooling results underpin the moment calculations (G12). The 136 evaluations are *related specializations* of one symmetric polynomial, not 136 independent scientific discoveries.

**Checked inventory when validated at the final source head:** 3,116 proof scripts, 3,102 public theorem/lemma/example statements, 3,414 documented declarations, across 37 modules. The symbolic ten-entry covariance form does **not** assert feasibility for arbitrary real matrix inputs: PSD is proved only for matrices constructed from nonnegative-weight finite samples. The report's general random-variable expectation theory, Gaussian conditional distributions, normal tails, chi-square pivots, independent binomial laws, interval coverage, Monte Carlo accuracy, and empirical IQ-model assumptions remain outside these finite/algebraic statements.

## D046x status — kernel-checked arbitrary-list pooling, covariance and rate diagnostics

On [exact Rocq 9.2 CI at commit `469f2cb2ed`](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43847174190), the shared
[`ListPoolingAlgebra.v`](../library/rocq/ListPoolingAlgebra.v) contributes
**159 new theorem proofs and 16 definitions**. The audit also passes the
strict source-order documentation gate, canonical library ownership check
and no-extra-axiom/no-unfinished-proof gate. The accepted corpus now contains
**2,947 proof scripts across 36 modules** (2,933 public theorems/lemmas/examples,
one earlier local helper, 13 model/record constructors), and **3,242
documented declarations**. Each proof is counted once, although all six
volumes may import shared results.

**Actual report links.** `sm:pooling` / G12 is now supported by
arbitrary finite lists of weighted group summaries: first/second moments,
weighted means, permutation/concatenation identities, exact
centered-sum-of-squares and ANOVA decompositions, mean minimization,
cross-moments and covariance transformations. `sm:binomial` / G08 and
`sm:rare` / G13 receive finite-list ideal heterogeneous Bernoulli
count/variance expressions, sharp upper bounds, rate sensitivity and
zero/equality criteria. Towers admissions receives the same
*deterministic* heterogeneous-rate diagnostics. These are meaningful
extensions beyond D043x two-group, D044x three-group and D045x
three-cohort formulas.

**Boundary:** the full report statements remain **partially
formalized** where they require stochastic facts. No independent-trial
binomial PMF, random-denominator conditional count law, Gaussian
conditioning/tail theorem, normal-sample chi-square pivot, exact interval
coverage, pseudorandom simulation guarantee or empirical IQ model is
derived from arbitrary-list algebra. For all 159 new scripts see the
[dedicated exact source-order refactoring register](PROOF_REFACTOR_LIST_POOLING.md);
the large historical register is retained for older modules. AI disclosure:
OpenAI ChatGPT assisted theorem specification, Rocq proof scripts, algebraic library reuse, documentation, CI diagnosis and source refactoring. Only explicitly stated Rocq propositions checked by the pinned kernel are mathematical proofs. No stochastic model, confidence coverage, empirical IQ validity or independent human validation is inferred.

## D045x status — stratified Bernoulli diagnostics and sharp variance bounds

A [Rocq 9.2 kernel validation](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43832111166) on exact commit
[`028d427d74a6fd8d81d9060d1feaa68aecbf96db`](https://github.com/AndersH3/composite_iq_checked_claims/commit/028d427d74a6fd8d81d9060d1feaa68aecbf96db)
certified **185 further source-documented theorems** in
[`StratifiedBernoulli.v`](../library/rocq/StratifiedBernoulli.v).
All three cohort count, failure-count, ideal Bernoulli variance, rate
second moment, squared calibration loss and pairwise rate-dispersion
definitions are shared rather than report-local. The sharp
four-times-variance bound, moment decomposition of rate dispersion,
nonnegativity and benchmark/error sensitivities help audit G08/G13
(`sm:binomial`, `sm:rare`) and Towers admission-rate contrasts.

**Scope boundary:** no binomial PMF, independence theorem,
conditional-count sampling distribution, Gaussian tail/conditional law,
chi-square pivot, interval coverage or arbitrary-length pooled sample
distribution is proved. In particular, the source-labelled report
classification remains partial (A) for `sm:binomial` and
`sm:rare`. The new 185 theorem proofs are deterministic real
algebra, including related cohort-wise specializations; do not
count each as a different stochastic law. The audited repository now
has **2,788 proof scripts in 35 modules**, 2,774 public claims and
3,067 fully documented declarations. Mathematical development and
this register were AI-assisted; exact statements are certified by
Rocq rather than the narrative.

## D044x status — extended three-replicate ANOVA and multi-rate precision

On exact source commit [`491ad9bbe79d2a1e8b6739885248ef06657cb307`](https://github.com/AndersH3/composite_iq_checked_claims/commit/491ad9bbe79d2a1e8b6739885248ef06657cb307),
[Rocq 9.2 kernel CI](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43819739947) proved **111 new, documented, reusable
real-algebra theorems** in two shared modules:

| Shared source | Theorems | Six-volume audit coverage | Outstanding gap |
|---|---:|---|---|
| [`ThreeGroupPooling.v`](../library/rocq/ThreeGroupPooling.v) | **39** | `sm:pooling` G12: real-valued three-replicate weighted mean, corrected SS, two-stage associativity and nonnegative variance | Arbitrary nonempty **list** of groups; sampling distribution of pooled statistic |
| [`TwoRatePrecision.v`](../library/rocq/TwoRatePrecision.v) | **72** | `sm:binomial`, `sm:rare` G08/G13, Towers rate contrasts: explicit hypothetical Bernoulli moment formulas, sensitivity and sharp variance gaps | Independent-trial binomial PMF, random-denominator sampling, interval coverage |
| **Total** | **111** | 6 report books reuse the same two modules; repeated import does not multiply theorem count | Gaussian tails, exact conditional distributions, normal sample chi-square pivots |

The original D042x **70 source-labelled statements** and 104 equation
anchors retain their source-scan identity. The D043x partial-coverage
classification remains appropriate: D044x extends the already partially
formalized portions of `sm:pooling`, `sm:binomial`, `sm:rare`, but does
not completely establish their report-level stochastic theorems. The
real-algebra statements are not promoted to full confidence-coverage,
sampling or IQ-population conclusions.

This mathematical documentation and proof development were AI-assisted; mathematical validity applies only to explicit Rocq propositions accepted by the pinned kernel. Neither empirical IQ assumptions nor stochastic sampling distributions are proved by these real-algebra results.

## D043x status update — exact statistical algebra (kernel checked)

The D042x source scan and its statement-location counts below are preserved as
the audit baseline. The following **new** Rocq results have since been
checked with Rocq 9.2 on commit
[`955379823a469ff57e8eb5f2320994697c7d5ef0`](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43812796040):

| Module | New theorem proofs | Specific six-volume obligations newly supported | Boundary still open |
|---|---:|---|---|
| [WilsonScoreAlgebra.v](../library/rocq/WilsonScoreAlgebra.v) | 36 | `sm:wilson` exact completed-square inversion, endpoints and symmetric/range constraints | Wilson coverage is nominal/approximate, not an exact finite-sample theorem |
| [SamplingPrecision.v](../library/rocq/SamplingPrecision.v) | 45 | `sm:binomial`, `sm:rare`: exact moment expressions, finite-sample precision and sample-count scaling | Independent-trial binomial distribution law and zero-count powers remain |
| [ConditionalRatioStability.v](../library/rocq/ConditionalRatioStability.v) | 30 | `tw:events`, `tw:quantization` and `sm:conditional-count`: ratio/positive-denominator algebra and sensitivity | Perturbed numerator/denominator simultaneous error certificate and random-denominator binomial law remain |
| [PooledMomentsAlgebra.v](../library/rocq/PooledMomentsAlgebra.v) | 31 | `sm:pooling`: exact two-batch within/between variance decomposition | Induction to arbitrary positive-size group lists and stochastic pooling law remain |
| **Total** | **142** | Common reusable definitions across the six report books | No normal-tail, Gaussian-conditioning, chi-square-pivot, Clopper–Pearson or empirical model claim is upgraded |

The original `P` status of `sm:wilson` in the D042x ledger below should
now be read as **A (partially formalized)**: its exact quadratic inversion is
kernel checked; its coverage interpretation is still not a Rocq theorem.
The other 69 source-labelled statements retain their D042x classifications
unless an exact report-level theorem is newly mapped. Accordingly the current
scoped ledger distribution is **F=8, A=38, P=23, L=1**, rather than
the historical D042x **F=8, A=37, P=24, L=1**. Since the shared `sm:wilson`
result appears in five volumes, the current per-volume appearances are
**F=19, A=75, P=59, L=1**, still 154 total; these are not distinct theorems.

The full stochastic and numerical error-certificate acceptance criteria in
packages G07–G13, G19–G24 remain. No Python/Deal or SPARK execution result
can substitute for a Rocq proof of a Gaussian or binomial probability law.

## The six reports

| ID | Report | Authoritative source | Linked PDF |
|---|---|---|---|
| **HF-M** | Hoeflin/Ferguson analytical | [`composite_iq_analysis.tex`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex) | [PDF](../analyses/hoeflin-ferguson/output/pdf/composite_iq_analysis.pdf) |
| **HF-S** | Hoeflin/Ferguson simulation | [`hoeflin_simulations.tex`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex) | [PDF](../analyses/hoeflin-ferguson/output/pdf/hoeflin_simulations.pdf) |
| **TW-M** | Towers analytical | [`towers_admissions_analysis.tex`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) | [PDF](../analyses/towers-multiple-test-admissions/output/pdf/towers_admissions_analysis.pdf) |
| **TW-S** | Towers simulation | [`towers_simulations.tex`](../analyses/towers-multiple-test-admissions/towers_simulations.tex) | [PDF](../analyses/towers-multiple-test-admissions/output/pdf/towers_simulations.pdf) |
| **SQ-M** | Sequential analytical | [`sequential_conditional_means.tex`](../analyses/sequential-conditional-means/sequential_conditional_means.tex) | [PDF](../analyses/sequential-conditional-means/output/pdf/sequential_conditional_means.pdf) |
| **SQ-S** | Sequential simulation | [`sequential_simulations.tex`](../analyses/sequential-conditional-means/sequential_simulations.tex) | [PDF](../analyses/sequential-conditional-means/output/pdf/sequential_simulations.pdf) |

**Verification codes:** **F** = existing finite/algebraic Rocq theorem directly covers that limited counterpart (not any broader stochastic wording); **A** = some exact covariance, regression, induction, finite event or arithmetic part is proved, but a substantive report claim remains; **P** = written TeX proof/reference exists, but no matching Rocq theorem for the full proposition was identified; **L** = direct Rocq Stdlib theorem (do not reinvent). A model choice, statistical output, numerical approximation or empirical claim is not by itself a universal proof obligation. **None** of F/A should be promoted to a general Gaussian probability theorem without the missing bridge.

## Coverage by actual report volume

These are **per-volume appearances** of labelled formal statements after resolving shared proof inputs, not distinct theorem obligations. Shared propositions are counted once in the 70-result unique-source total, and multiple statements within one proposition can require multiple Rocq lemmas.

| Report | Linked proof statements | F (finite scope) | A (partial) | P (report only) | L (Stdlib) | Body equation anchors |
|---|---:|---:|---:|---:|---:|---:|
| HF-M — Hoeflin analytical | 25 | 4 | 10 | 11 | 0 | 17 |
| HF-S — Hoeflin simulation | 25 | 4 | 10 | 11 | 0 | 7 |
| TW-M — Towers analytical | 27 | 3 | 11 | 13 | 0 | 17 |
| TW-S — Towers simulation | 27 | 3 | 11 | 13 | 0 | 6 |
| SQ-M — Sequential analytical | 30 | 3 | 19 | 7 | 1 | 50 |
| SQ-S — Sequential simulation | 20 | 2 | 9 | 9 | 0 | 7 |
| **Total appearances** | **154** | **19** | **70** | **64** | **1** | **104** |

The number of unique source statements is **70**, not 154. In the same way, the **104** labelled equations are equation anchors, not 104 independent unproved theorems. The proof backlog below represents 24 reusable mathematical work packages, several of which will require numerous distinct Rocq statements.

## Source-by-source theorem/proposition inventory

The following register enumerates **every labelled `theorem`, `lemma`, `proposition` and `corollary` environment** found in the eleven proof-bearing source files, counting shared imports only once. Individual rows can contain multiple logically independent subclaims, so they do not represent one-to-one new Rocq theorems.

### [`reporting/proof_foundations.tex`](../reporting/proof_foundations.tex) — 7 statements

*Used in:* HF-M, HF-S, TW-M, TW-S, SQ-S.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`pf:moments`](../reporting/proof_foundations.tex#L31) | Finite moments and affine changes of scale | **F** | FiniteMoments weighted covariance and affine identities; finite zero-support result | `G01` |
| [`pf:spectral`](../reporting/proof_foundations.tex#L62) | Covariance feasibility and Gaussian construction | **A** | EquicorrelationVectors finite PSD/PD characterization only | `G02` |
| [`pf:gaussian`](../reporting/proof_foundations.tex#L90) | Gaussian closure and block independence | **P** | No Gaussian probability-space construction | `G02` |
| [`pf:conditioning`](../reporting/proof_foundations.tex#L114) | Gaussian conditional distribution and exact histories | **P** | TwoObservationSchur/EquicorrelationInverseVectors check algebra, not Gaussian kernels | `G03`, `G04` |
| [`pf:normal-marginals`](../reporting/proof_foundations.tex#L150) | Normal marginals do not imply joint normality | **P** | ReportCounterexample supplies a different finite discrete witness | `G05` |
| [`pf:events`](../reporting/proof_foundations.tex#L172) | Event arithmetic, ratios and indicator phi | **F** | FiniteUnion; Admissions; FiniteBridge under finite normalization and positive denominators | `G06` |
| [`pf:expectation`](../reporting/proof_foundations.tex#L196) | Tower property and population-conditional variance | **A** | FiniteTwoCellProjection, FiniteNestedProjection, FiniteConditionalResidual only | `G06` |

### [`reporting/statistical_methods.tex`](../reporting/statistical_methods.tex) — 9 statements

*Used in:* HF-M, HF-S, TW-M, TW-S, SQ-S.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`sm:normal-sample`](../reporting/statistical_methods.tex#L15) | Independent Gaussian sample moments and chi-square pivot | **P** | No normal-sample or chi-square distribution theorem in current modules | `G07` |
| [`sm:sd-interval`](../reporting/statistical_methods.tex#L42) | SD confidence intervals and reference bands | **P** | No chi-square quantile/pivot coverage proof | `G07` |
| [`sm:binomial`](../reporting/statistical_methods.tex#L69) | Bernoulli count law, expectation and variance | **A** | Finite event mass arithmetic; independent-trial binomial law missing | `G08` |
| [`sm:wilson`](../reporting/statistical_methods.tex#L86) | Wilson score endpoints and coverage scope | **P** | No Rocq score-inequality inversion theorem | `G09` |
| [`sm:clopper-pearson`](../reporting/statistical_methods.tex#L117) | Exact equal-tail binomial interval coverage | **P** | No exact conservative binomial-tail coverage proof | `G10` |
| [`sm:conditional-count`](../reporting/statistical_methods.tex#L151) | Conditional binomial given random denominator | **P** | Finite event conditioning only; no independent trial count conditioning | `G11` |
| [`sm:pooling`](../reporting/statistical_methods.tex#L178) | Pooled sample counts and variance identity | **A** | FiniteMoments variance tools only; full grouped sample identity not matched | `G12` |
| [`sm:multiple`](../reporting/statistical_methods.tex#L205) | Simultaneous diagnostic union bound | **A** | FiniteUnion arbitrary union bound, not general diagnostic probability model | `G13` |
| [`sm:rare`](../reporting/statistical_methods.tex#L221) | Zero counts and rare-event precision scaling | **A** | Elementary real/event algebra; independent binomial sampling law absent | `G08`, `G13` |

### [`analyses/hoeflin-ferguson/proofs_hoeflin.tex`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex) — 9 statements

*Used in:* HF-M, HF-S.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`hfpr:standardization`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L20) | Covariance, scales and weighted composites | **F** | FiniteMoments; Hoeflin.normalized_variance_is_one; affine identities | `G01` |
| [`hfpr:equal-weights`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L53) | Equal weights and PSD feasibility | **F** | Hoeflin.equal_weight_variance; EquicorrelationVectors PSD criterion | `G01` |
| [`hfpr:normality`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L102) | Joint Gaussian assumption needed for percentile claims | **P** | No Gaussian affine standard-normal composite proof | `G02`, `G05` |
| [`hfpr:thresholds`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L132) | Threshold monotonicity and asymptotic variance floor | **A** | Hoeflin variance monotonicity and epsilon variance bound | `G14` |
| [`hfpr:factor`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L199) | Common-factor aggregate, posterior and residual | **A** | Hoeflin posterior variance arithmetic; finite regression/Schur algebra | `G03`, `G15` |
| [`hfpr:nonidentification`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L268) | Observable scores do not identify latent ability | **P** | No matching latent-variable same-observation countermodel | `G16` |
| [`hfpr:selection`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L288) | Selection and repeated-score effects | **P** | Finite two-stratum association only; no continuous/test-retry theorem | `G16` |
| [`hfpr:simulation`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L341) | Cross-size coupling, rare-event precision, exponential bounds | **A** | Finite event algebra, composite variance; distributional coupling and exponential bound open | `G08`, `G17` |
| [`hfpr:numerics`](../analyses/hoeflin-ferguson/proofs_hoeflin.tex#L401) | Exact composite and latent example arithmetic | **A** | Hoeflin.standardized_160_sd16 and rational latent algebra | `G14`, `G18` |

### [`analyses/towers-multiple-test-admissions/proofs_towers.tex`](../analyses/towers-multiple-test-admissions/proofs_towers.tex) — 11 statements

*Used in:* TW-M, TW-S.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`tw:gaussian`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L17) | Bivariate Gaussian density and joint exceedance tail | **P** | TwoObservationSchur only gives covariance algebra | `G02`, `G19` |
| [`tw:events`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L56) | Four cells, positive conditional denominators, binary phi | **F** | Admissions, FiniteUnion, FiniteBridge; normalized indicator phi | `G06` |
| [`tw:plackett`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L99) | Plackett correlation derivative and sensitivity | **P** | No Gaussian differentiation-under-the-integral theorem | `G19` |
| [`tw:original-bound`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L140) | Historical contradiction and strict Gaussian lower bound | **A** | Union ≤ sum is finite-checked; strict analytic Gaussian lower bound absent | `G19`, `G20` |
| [`tw:nesting`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L198) | Same-score threshold nesting vs different-score nonnesting | **A** | Finite event containment; Gaussian joint positive density missing | `G19` |
| [`tw:calibration`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L221) | Unique OR-tail calibrated cutoff | **P** | No normal tail continuity and strict monotonicity result | `G20` |
| [`tw:rarity`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L243) | Normal rarity-equivalent cutoff is not a population identifier | **P** | Normal CDF inverse and different-selection law absent | `G14`, `G16` |
| [`tw:attempts`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L273) | Several routes and selection dependence | **A** | FiniteUnion union bound and finite association; selected Gaussian cohort not proved | `G08`, `G16` |
| [`tw:grid`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L299) | Finite BASIC grid probability and midpoint offset | **A** | Admissions.grid_scale_factors_cancel; FiniteSum, but not complete grid proof | `G21` |
| [`tw:quantization`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L350) | Conditional ratio perturbation bound | **P** | No matching named Rocq theorem | `G21` |
| [`tw:simulation`](../analyses/towers-multiple-test-admissions/proofs_towers.tex#L371) | Four-cell sample counts and selected denominators | **A** | Finite admission event partition; conditional-binomial law absent | `G11` |

### [`analyses/sequential-conditional-means/theorem_foundations.tex`](../analyses/sequential-conditional-means/theorem_foundations.tex) — 7 statements

*Used in:* SQ-M.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`thm:moments`](../analyses/sequential-conditional-means/theorem_foundations.tex#L15) | Moment identities and zero variance | **F** | FiniteMoments finite probability and covariance identities | `G01` |
| [`thm:conditional`](../analyses/sequential-conditional-means/theorem_foundations.tex#L57) | Conditional expectation and total variance | **A** | FiniteTwoCellProjection and finite covariance/residual libraries | `G06` |
| [`thm:spectral`](../analyses/sequential-conditional-means/theorem_foundations.tex#L114) | Spectral PSD and Gaussian covariance construction | **A** | EquicorrelationVectors all finite-list PSD/PD criteria only | `G02` |
| [`thm:gaussian`](../analyses/sequential-conditional-means/theorem_foundations.tex#L137) | Gaussian affine transformation, independent blocks | **P** | No normal-vector probability theorem | `G02` |
| [`thm:regression`](../analyses/sequential-conditional-means/theorem_foundations.tex#L169) | Gaussian nonsingular-block regression | **A** | TwoObservationSchur, EquicorrelationInverseVectors, TrivariateSchur algebra | `G03` |
| [`lem:continuous-version`](../analyses/sequential-conditional-means/theorem_foundations.tex#L204) | Unique continuous conditional-mean version | **P** | No continuous probability-kernel uniqueness theorem | `G04` |
| [`thm:induction`](../analyses/sequential-conditional-means/theorem_foundations.tex#L230) | Mathematical induction | **L** | Stdlib nat_ind; no bespoke induction scheme needed | — |

### [`analyses/sequential-conditional-means/sequential_conditional_means.tex`](../analyses/sequential-conditional-means/sequential_conditional_means.tex) — 12 statements

*Used in:* SQ-M.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`prop:domain`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L114) | Equicorrelation domain and Gaussian realization | **A** | EquicorrelationVectors.vector_equicorrelation_psd_iff, pd_iff; no Gaussian construction | `G02` |
| [`thm:equicorrelated-conditioning`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L167) | Gaussian conditioning for all fixed histories | **A** | SequentialReport residual algebra; EquicorrelationInverseVectors inverse action | `G03`, `G04` |
| [`thm:single-start`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L268) | One fixed starting score and recursive average | **A** | SequentialReport full-history induction and mean; Gaussian regression law absent | `G03` |
| [`prop:population-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L366) | Unconditioned population mean variance and SD | **F** | Hoeflin and FiniteMoments equal-weight variance; SequentialReport match | `G01` |
| [`prop:conditional-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L410) | SD of mean given initial score | **A** | SequentialReport.sequential_conditional_variance_one_start; Gaussian conditioning unproved | `G03` |
| [`thm:multiple-mean`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L559) | Multiple equal fixed starts and predicted inclusive mean | **A** | SequentialReport.sequential_recursive_prediction_constant and inclusive_mean_closed_form | `G03` |
| [`thm:multiple-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L609) | Population and conditional spreads for r observed scores | **A** | Finite quadratic form and SequentialReport residual identity, not Gaussian law | `G03` |
| [`cor:two-starts`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L688) | Two-start prediction and mean | **A** | SequentialReport.sequential_prediction_two_starts and mean_two_starts | `G03` |
| [`cor:three-starts`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L719) | Three-start prediction and mean | **A** | SequentialReport.sequential_prediction_three_starts and mean_three_starts | `G03` |
| [`prop:multiple-boundaries`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L752) | Singular and independent boundary cases | **A** | SequentialReport singular-boundary and c=1/0 arithmetic; compatible Gaussian histories open | `G04` |
| [`cor:iq-reporting`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L822) | Affine IQ score transformation | **A** | SequentialReport.sequential_iq_prediction_exact and mean_exact; end-to-end root rounding open | `G18` |
| [`prop:counterexample`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L1001) | Marginals/correlation do not determine conditional means | **F** | ReportCounterexample finite rational witness; report example may differ | — |

### [`analyses/sequential-conditional-means/asymptotic_limits.tex`](../analyses/sequential-conditional-means/asymptotic_limits.tex) — 5 statements

*Used in:* SQ-M.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`prop:limit-domain`](../analyses/sequential-conditional-means/asymptotic_limits.tex#L11) | Admissible fixed c for arbitrarily large n | **A** | Finite vector PSD/PD criterion; explicit unbounded-size proof needed | `G22` |
| [`lem:square-root-limit-bound`](../analyses/sequential-conditional-means/asymptotic_limits.tex#L28) | Nonnegative square-root limit bound | **P** | Stdlib.sqrt lemmas available but exact statement not identified | `G22` |
| [`thm:prediction-limits`](../analyses/sequential-conditional-means/asymptotic_limits.tex#L46) | Prediction, inclusive mean and both SD limits | **A** | SequentialSensitivity finite identities; no full real epsilon convergence proof | `G22` |
| [`prop:gaussian-limit-coupling`](../analyses/sequential-conditional-means/asymptotic_limits.tex#L113) | L2 convergence of Gaussian aggregate coupling | **P** | No Gaussian L2 coupling theorem | `G23` |
| [`cor:iq150-limits`](../analyses/sequential-conditional-means/asymptotic_limits.tex#L138) | IQ150 limit values and units | **A** | Exact rational IQ coefficients; real sqrt/infinite limits open | `G18`, `G22` |

### [`analyses/sequential-conditional-means/sd_interpretation.tex`](../analyses/sequential-conditional-means/sd_interpretation.tex) — 2 statements

*Used in:* SQ-M.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`prop:variance-components-general`](../analyses/sequential-conditional-means/sd_interpretation.tex#L42) | Random starting block contribution / law of total variance | **A** | FiniteConditionalCovariance and finite projection; Gaussian block law open | `G03`, `G06` |
| [`prop:conditional-sd-growth-examples`](../analyses/sequential-conditional-means/sd_interpretation.tex#L105) | Conditional SD increases for c=3/5 at every k | **P** | Related SequentialSensitivity theorems, no direct all-k strict-growth theorem identified | `G22` |

### [`analyses/sequential-conditional-means/exact_numeric_certificates.tex`](../analyses/sequential-conditional-means/exact_numeric_certificates.tex) — 2 statements

*Used in:* SQ-M.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`cor:exact-iq-values`](../analyses/sequential-conditional-means/exact_numeric_certificates.tex#L11) | Exact IQ means and squared SDs | **A** | SequentialReport exact IQ formulas, not end-to-end root/cast certificate | `G18` |
| [`lem:rounding`](../analyses/sequential-conditional-means/exact_numeric_certificates.tex#L91) | Exact rational and square-root rounding rules | **A** | ReportRounding soundness + nine exact row certificates; composition remains | `G18` |

### [`analyses/sequential-conditional-means/computational_verification.tex`](../analyses/sequential-conditional-means/computational_verification.tex) — 2 statements

*Used in:* SQ-M.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`prop:simulation-reference-laws`](../analyses/sequential-conditional-means/computational_verification.tex#L104) | Normal-sample pivot laws in main report | **P** | No normal sample mean/chi-square pivot theorem | `G07` |
| [`cor:simulation-diagnostic-coverage`](../analyses/sequential-conditional-means/computational_verification.tex#L131) | SD bands and finite diagnostic coverage | **P** | Finite union inequality only; Gaussian chi-square inversion absent | `G07`, `G13` |

### [`analyses/sequential-conditional-means/proof_completion_sequential.tex`](../analyses/sequential-conditional-means/proof_completion_sequential.tex) — 4 statements

*Used in:* SQ-S.

| Label / original source line | Statement | Scope | Existing Rocq evidence / remaining boundary | Outstanding proof packages |
|---|---|---|---|---|
| [`seqp:domain`](../analyses/sequential-conditional-means/proof_completion_sequential.tex#L11) | Finite and unbounded Gaussian correlation domains | **A** | EquicorrelationVectors finite criterion; Gaussian existence/limit separate | `G02`, `G22` |
| [`seqp:conditioning`](../analyses/sequential-conditional-means/proof_completion_sequential.tex#L38) | Conditional future law at exact point histories | **P** | Schur covariance algebra exists; Gaussian conditional vector law not proved | `G03`, `G04` |
| [`seqp:recursion`](../analyses/sequential-conditional-means/proof_completion_sequential.tex#L109) | Recursive predictions and two Gaussian aggregate laws | **A** | SequentialReport prediction induction; Gaussian aggregate law missing | `G03` |
| [`seqp:variance-decomposition`](../analyses/sequential-conditional-means/proof_completion_sequential.tex#L154) | Population and conditional SD with random histories | **A** | Finite total variance and regression algebra, no Gaussian conditioning | `G03`, `G06` |

**Statement ledger: 70 labelled results across 11 proof-bearing sources; scoped counts F=8, A=37, P=24, L=1.** The full report status is never inferred from a previously checked formula with weaker premises, different stochastic model or finite-only scope.

## Per-report equation and unlabelled proof obligations

### HF-M

| Claim family | Anchors/inputs (within original volume) | Formalization decision |
|---|---|---|
| Variance and covariance of weighted composites; equal weights | `eq:variance-sum, eq:weighted-variance, eq:average-correlation, eq:mean-variance` | Finite covariance proofs F; general moments G01. |
| Normal quantiles, thresholds, n-limit, reported percentile | `eq:quantile, eq:threshold, eq:limit` | Normal quantile existence G14; certified values G24; limit G22 analog. |
| Latent factor conditional posterior and nonidentification | `eq:factor-model, eq:factor-reliability, eq:latent-mean, eq:latent-variance` | Reliability algebra A; stochastic posterior G03/G15 and countermodel G16. |
| IQ-scale affine conversion, worked SD-16 example | `eq:reporting-scale, eq:iq-composite, eq:worked-example` | Affine algebra F; complete integer/sqrt rounding G18. |

### HF-S

| Claim family | Anchors/inputs (within original volume) | Formalization decision |
|---|---|---|
| Normal-score simulation factor and aggregate equality in distribution | `eq:hf-factor-model, eq:hf-average-variance, eq:hf-aggregate` | Variance F/A; Gaussian joint law and coupled shortcuts G02/G15/G17. |
| Composite normal tails at 2, 3 and one-in-a-million q | `eq:hf-composite, eq:hf-tail-targets` | Normalization F; CDF/quantiles G14 and certified tails G24. |
| Factor predictor, conditional variance and MSE | `eq:hf-predictor, eq:hf-mse` | Schur and rational MSE A; Gaussian posterior/optimality G03/G15. |
| Observed tail/replicate tables and binomial/Wilson/CP diagnostics | `simulation-data/tails.tex, moments.tex, replicates.tex` | Sampling laws G07–G13; recorded seed-dependent counts remain execution evidence. |

### TW-M

| Claim family | Anchors/inputs (within original volume) | Formalization decision |
|---|---|---|
| Bivariate normal model, density, conditional tail and rho integral | `eq:model, eq:joint, eq:rho-integral` | Covariance identities A; Gaussian distribution/integral G19. |
| OR, conditional ratios, binary phi and Fréchet/union bounds | `eq:union, eq:conditionals, eq:phi, eq:bounds` | Finite normalized admissions F; explicit positive denominators. |
| Equal/mixed thresholds, conditional numerators and historical bound | `eq:equal-results, eq:mixed-joint, eq:mixed-conditionals, eq:repeat-pass` | Ratios F; Gaussian numeric values and strict bound G19/G20/G24. |
| Normal rarity equivalent and calibrated OR/AND cutoffs | `eq:rarity, eq:calibration` | Gaussian quantile theory G14/G20; certified roots G24. |
| BASIC grid and error of rounded conditional ratios | `eq:grid` | FiniteSum/Admissions cancellation A; exact grid/ratio bounds G21. |

### TW-S

| Claim family | Anchors/inputs (within original volume) | Formalization decision |
|---|---|---|
| Correlated Gaussian generator and reference overlap integral | `eq:towers-generator, eq:towers-reference-integral` | Covariance algebra A; bivariate Gaussian density/integral G02/G19. |
| Union, selected denominators, binary phi | `eq:towers-union, eq:towers-conditionals, eq:towers-phi` | Admissions F; actual conditional-binomial sampling G11. |
| Calibrated 2% OR rule and quoted numerical cutoff | `eq:towers-calibration` | Existence/uniqueness G20; numerical enclosure G24. |
| Rare counts, exact/Wilson intervals, pooled groups, dependent rules | `simulation-data/events.tex, conditionals.tex, replicates.tex` | G07–G13; reused draws mean rule-specific results are dependent. |

### SQ-M

| Claim family | Anchors/inputs (within original volume) | Formalization decision |
|---|---|---|
| Covariance domain, spectral realization, inverse/regression | `eq:covariance, eq:domain, eq:inverse, eq:coefficient` | Finite PSD and inverse F; Gaussian construction/regression G02/G03. |
| Recursive prediction and inclusive mean | `eq:recursion, eq:answer, eq:multiple-recursion, eq:multiple-mean` | Induction and rational identities A; Gaussian conditional interpretation G03. |
| Population versus conditional variance and SD, all r starts | `eq:population-variance, eq:conditional-variance, eq:multiple-conditional-variance` | Finite covariance F/A; conditional normal law G03/G04. |
| Singular endpoints, limits and compatible histories | `prop:multiple-boundaries, prop:limit-domain, thm:prediction-limits` | Singular algebra A; measure support G04 and epsilon/sqrt limits G22. |
| IQ150 exact values and nine printed rounded cases | `eq:iq150-mean, eq:iq150-population-sd, eq:iq150-conditional-sd` | Rational formula + nine certificates A; end-to-end roots/casts G18. |
| Sample-mean chi-square and diagnostic coverage (computational appendix) | `prop:simulation-reference-laws, cor:simulation-diagnostic-coverage` | No distributional chi-square pivot or coverage theorem; G07/G13. |

### SQ-S

| Claim family | Anchors/inputs (within original volume) | Formalization decision |
|---|---|---|
| Common-factor Gaussian prior, recursive conditional center | `eq:seq-sim-factor, eq:seq-sim-centre` | Deterministic recurrence A; Gaussian regression G02/G03. |
| Population and conditional future vector/aggregate laws | `eq:seq-sim-population, eq:seq-sim-conditional, eq:seq-sim-posterior-factor, eq:seq-sim-future-vector` | Covariance algebra A; pointwise conditional Gaussian vector G03/G04. |
| Positive finite difference and infinite conditional SD limits | `eq:seq-sim-limit-sds, sec:seq-sim-monotonicity` | Strict monotonicity G22; Gaussian L2 limit coupling G23. |
| Replicate intervals, chi-square and rare-event diagnostics | `simulation-data/means.tex, sds.tex, limits.tex, replicates.tex` | G07–G13; observed draws/PRNG independence not formal assumptions. |

The claim/evidence maps were also read: `analyses/hoeflin-ferguson/claimmap_hoeflin.tex`, `claimmap_hoeflin_simulations.tex`, `analyses/towers-multiple-test-admissions/claimmap_towers.tex`, `claimmap_towers_simulations.tex`, and `analyses/sequential-conditional-means/claimmap_sequential_simulations.tex`. The Sequential main report has an embedded claim map. These are **classification/evidence indexes** rather than additional formally quantified theorem environments.

## New and incomplete Rocq proof packages (unique, not per-report duplicates)

| Package | Priority | Requirement (exact mathematical scope) |
|---|---|---|
| `G01` | **P1** | **General square-integrable moments.** Bridge finite covariance to general L2 moments and zero-variance a.s. using maintained probability libraries. |
| `G02` | **P0** | **Gaussian vector construction and closure.** Prove affine Gaussian closure, block independence, PSD-to-Gaussian covariance realization and singular cases. |
| `G03` | **P0** | **Gaussian block regression and future conditional laws.** Prove multivariate Gaussian conditional mean/covariance, residual independence, Hoeflin factor and Sequential predictions. |
| `G04` | **P0** | **Pointwise Gaussian regular conditionals.** Construct exact-history conditional kernel, continuity/uniqueness on full support, compatible singular endpoints. |
| `G05` | **P2** | **Normal-marginal non-joint countermodel.** Prove sign-mixture normal marginals and non-Gaussian joint law with designated correlation and distinct joint tails. |
| `G06` | **P1** | **General conditional-expectation theory.** Formalize L1/L2 existence, tower, pull-out and total variance and bridge finite event counterparts. |
| `G07` | **P1** | **Normal sample and chi-square pivots.** Independent normal sample mean, sample variance pivot, mean/variance independence, exact SD confidence and reference intervals. |
| `G08` | **P1** | **Independent Bernoulli/binomial law.** Derive binomial PMF from independent trials, moments, zero counts, relative precision, equal-design pooling. |
| `G09` | **P1** | **Wilson score inversion.** Prove radical/quadratic inversion and endpoint inequalities, explicitly *not* exact nominal finite coverage. |
| `G10` | **P1** | **Clopper–Pearson exact coverage.** Endpoint uniqueness/monotone binomial tails, boundary counts, conservative coverage for all p. |
| `G11` | **P1** | **Conditional binomial with random denominator.** Prove N_AB conditional on N_A=l>0 follows Binomial(l, J/p_A); zero denominator excluded. |
| `G12` | **P2** | **Pooled sample variance decomposition.** Prove arbitrary finite group within/between sum-of-squares identity using existing finite sums. |
| `G13` | **P2** | **Multiple diagnostics and rare precision.** Bridge finite union to general false alarm events, and certify zero-count/relative sample-size inequalities. |
| `G14` | **P1** | **Normal CDF and quantile calculus.** Prove strict monotonicity, continuity, existence/uniqueness of tails and Hoeflin threshold effects. |
| `G15` | **P1** | **Hoeflin common-factor law and predictor.** Prove joint-law aggregate identity, exact factor posterior, contrasts and optimal L2 MSE from Gaussian conditioning. |
| `G16` | **P2** | **Latent nonidentification/selection/retesting.** Construct explicit same-observable latent countermodels, selected-sample dependence and repeated-attempt examples. |
| `G17` | **P2** | **Cross-size simulation coupling and exponential bounds.** Contrast common-residual coupling against nested battery, prove nested indicators and exp bounds for (1-p)^T. |
| `G18` | **P2** | **End-to-end exact arithmetic/rounding.** Compose nine SQ IQ-150 certificates, sqrt/cast/nearest rounding, Hoeflin worked examples. |
| `G19` | **P0** | **Bivariate Gaussian tail and Plackett identity.** Construct density and one-dimensional conditional integral J(a,b;rho); prove ∂J/∂rho=f_rho(a,b)>0. |
| `G20` | **P1** | **Towers strict bounds and unique OR calibration.** Obtain strict analytic tail bounds rejecting historical figures, and continuous strictly monotone calibrated OR cutoff. |
| `G21` | **P2** | **BASIC grid and conditional ratio error.** Prove grid 397² enumeration, offset and normalization; bound perturbed J/p ratios. |
| `G22` | **P2** | **Sequential real limits and growth.** Prove full epsilon SD limits, sqrt-continuity and strict conditional variance increase at c=3/5 for every k. |
| `G23` | **P2** | **Gaussian L2 aggregate coupling.** Using G02/G22, prove common-normal aggregate converges in mean-square, including zero variance. |
| `G24` | **P1** | **Certified tail/quantile numerical bounds.** Provide exact enclosure for Gaussian tails, calibrated roots and displayed values; SciPy/MC are not certificates. |

**Dependency and reuse order:** G02 → G03 → G04/G15/G23; G19 → G20 → G24; G08 → G09/G10/G11/G13; G07 → SD confidence/diagnostic results; G06 → general conditional-expectation corollaries. Reuse canonical `library/rocq/`, existing `FiniteSum`, `FiniteUnion`, `FiniteMoments`, `TwoObservationSchur`, `TrivariateSchur`, `EquicorrelationInverseVectors`, Rocq Stdlib, and established measure/probability libraries. Report-owned corollaries belong under the matching analysis project's `rocq/` directory. Do not add homegrown distribution axioms or create stand-ins that merely restate a claim as an assumption.

## Audit boundary, future rescan and acceptance

- This is a **TeX source audit** pinned to `5c23afcd48bd36302c0acd2bbdf75271abf06921`; the linked six PDFs were identified from the READMEs, but PDF binaries were **not** independently rendered or compared with the current source in this pass. Numerical tables and figure inputs remain model/execution evidence, not proof terms.
- The exhaustive named-environment count is **70** across eleven TeX files; the main SQ computational appendix contributes **two** claims that would otherwise be missed. Other mathematical claims in the six report bodies are grouped above; the audit does not miscount every displayed equation as a distinct needed theorem.
- For each completed package, add an exact Rocq proposition with explicit positivity, integrability, singularity and conditioning premises, map it to the original report label(s), build with pinned Rocq 9.2 and run the canonical documentation/placeholder/ownership gates. Mark **fully kernel proved** only when its exact report-level statement is established, not merely the coefficient algebra.
- Run the independent Python/Deal/SPARK checks for changes that affect those implementations. Keep model assumptions, numeric integration error, simulation records, external evidence and analytical theorem validity in separate categories. No amount of simulation establishes an empirical IQ distribution.
- Re-scan **all six volumes**, their eleven proof-bearing sources and the five claim maps after any material report edit. A source label or filename change must update this register and `rocq/REPORT_THEOREM_INVENTORY.md`.

## Exhaustive labelled-equation disposition index (six top-level books)

Unlike the preceding thematic matrix, this index gives a disposition for **every `eq:` anchor** in the six authoritatively linked source books. Status codes here are **D** = definition/assumption (no theorem merely by declaration); **F** = finite or real-algebraic counterpart exists at its limited scope; **A** = only an algebraic part is Rocq-proved, a stochastic/limit or presentation-level inference remains; **P** = mathematical Gaussian/distributional theorem absent; **N** = numeric model target requiring certified tail/quantile/root evaluation. Identical symbols may appear in multiple formulas; a label is not one independently unproved theorem. The task IDs explain what remains.

### HF-M: 17 distinct labels

| Exact source anchor | Disposition | Remaining proof task(s) |
|---|---|---|
| [`eq:variance-sum`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L55) | **F** | `G01` |
| [`eq:standardize`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L112) | **D** | Not a theorem on its own |
| [`eq:weighted-variance`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L132) | **F** | `G01` |
| [`eq:weighted-composite`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L137) | **D** | Not a theorem on its own |
| [`eq:average-correlation`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L152) | **D** | Not a theorem on its own |
| [`eq:mean-variance`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L163) | **F** | `G01` |
| [`eq:equal-composite`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L168) | **F** | `G01` |
| [`eq:reporting-scale`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L185) | **D** | Not a theorem on its own |
| [`eq:iq-composite`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L191) | **F** | `G01` |
| [`eq:worked-example`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L200) | **A** | `G14`, `G18` |
| [`eq:quantile`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L224) | **P** | `G14`, `G24` |
| [`eq:threshold`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L229) | **A** | `G14`, `G18` |
| [`eq:limit`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L281) | **A** | `G14`, `G18` |
| [`eq:factor-model`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L352) | **D** | Not a theorem on its own |
| [`eq:factor-reliability`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L363) | **A** | `G03`, `G15` |
| [`eq:latent-mean`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L368) | **A** | `G03`, `G15` |
| [`eq:latent-variance`](../analyses/hoeflin-ferguson/composite_iq_analysis.tex#L370) | **A** | `G03`, `G15` |

### HF-S: 7 distinct labels

| Exact source anchor | Disposition | Remaining proof task(s) |
|---|---|---|
| [`eq:hf-factor-model`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex#L91) | **D** | Not a theorem on its own |
| [`eq:hf-average-variance`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex#L103) | **F** | `G01` |
| [`eq:hf-aggregate`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex#L117) | **P** | `G02`, `G15`, `G17` |
| [`eq:hf-composite`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex#L141) | **F** | `G01` |
| [`eq:hf-tail-targets`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex#L152) | **P** | `G14`, `G24` |
| [`eq:hf-predictor`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex#L180) | **A** | `G03`, `G15` |
| [`eq:hf-mse`](../analyses/hoeflin-ferguson/hoeflin_simulations.tex#L191) | **A** | `G03`, `G15` |

### TW-M: 17 distinct labels

| Exact source anchor | Disposition | Remaining proof task(s) |
|---|---|---|
| [`eq:model`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L168) | **D** | Not a theorem on its own |
| [`eq:cutoffs`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L182) | **D** | Not a theorem on its own |
| [`eq:joint`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L188) | **P** | `G19` |
| [`eq:union`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L193) | **F** | `G06` |
| [`eq:conditionals`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L194) | **F** | `G06` |
| [`eq:phi`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L204) | **F** | `G06` |
| [`eq:equal-results`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L221) | **N** | `G19`, `G24` |
| [`eq:repeat-pass`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L228) | **F** | `G06` |
| [`eq:union-denominator`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L238) | **F** | `G06` |
| [`eq:mixed-joint`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L273) | **N** | `G19`, `G24` |
| [`eq:mixed-conditionals`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L278) | **N** | `G19`, `G24` |
| [`eq:mixed-remainder`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L280) | **N** | `G19`, `G24` |
| [`eq:rarity`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L311) | **P** | `G14`, `G20`, `G24` |
| [`eq:calibration`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L325) | **P** | `G14`, `G20`, `G24` |
| [`eq:bounds`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L356) | **F** | `G06` |
| [`eq:grid`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L386) | **A** | `G21` |
| [`eq:rho-integral`](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex#L465) | **P** | `G19` |

### TW-S: 6 distinct labels

| Exact source anchor | Disposition | Remaining proof task(s) |
|---|---|---|
| [`eq:towers-union`](../analyses/towers-multiple-test-admissions/towers_simulations.tex#L64) | **F** | `G06` |
| [`eq:towers-conditionals`](../analyses/towers-multiple-test-admissions/towers_simulations.tex#L67) | **F** | `G06` |
| [`eq:towers-generator`](../analyses/towers-multiple-test-admissions/towers_simulations.tex#L116) | **P** | `G02`, `G19` |
| [`eq:towers-reference-integral`](../analyses/towers-multiple-test-admissions/towers_simulations.tex#L161) | **P** | `G02`, `G19` |
| [`eq:towers-calibration`](../analyses/towers-multiple-test-admissions/towers_simulations.tex#L365) | **N** | `G20`, `G24` |
| [`eq:towers-phi`](../analyses/towers-multiple-test-admissions/towers_simulations.tex#L430) | **F** | `G06` |

### SQ-M: 50 distinct labels

| Exact source anchor | Disposition | Remaining proof task(s) |
|---|---|---|
| [`eq:standardization`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L72) | **D** | Not a theorem on its own |
| [`eq:first`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L84) | **D** | Not a theorem on its own |
| [`eq:definition`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L87) | **D** | Not a theorem on its own |
| [`eq:target`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L92) | **D** | Not a theorem on its own |
| [`eq:covariance`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L126) | **D** | Not a theorem on its own |
| [`eq:domain`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L133) | **A** | `G02`, `G03`, `G04` |
| [`eq:factor`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L153) | **D** | Not a theorem on its own |
| [`eq:inverse`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L195) | **F** | `G01` |
| [`eq:coefficient`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L210) | **A** | `G02`, `G03`, `G04` |
| [`eq:residual`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L217) | **A** | `G02`, `G03`, `G04` |
| [`eq:conditional-mean`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L239) | **A** | `G02`, `G03`, `G04` |
| [`eq:conditional-variance`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L260) | **A** | `G02`, `G03`, `G04` |
| [`eq:recursion`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L282) | **A** | `G03` |
| [`eq:all-predictions`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L294) | **A** | `G03` |
| [`eq:answer`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L301) | **A** | `G03` |
| [`eq:total-count`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L312) | **A** | `G03` |
| [`eq:fixed-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L359) | **F** | `G01` |
| [`eq:actual-average`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L376) | **D** | Not a theorem on its own |
| [`eq:population-variance`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L389) | **F** | `G01` |
| [`eq:population-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L396) | **F** | `G01` |
| [`eq:population-sd-total`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L402) | **F** | `G01` |
| [`eq:actual-mean`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L432) | **A** | `G02`, `G03`, `G04` |
| [`eq:actual-variance`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L440) | **A** | `G02`, `G03`, `G04` |
| [`eq:conditional-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L446) | **A** | `G02`, `G03`, `G04` |
| [`eq:conditional-sd-total`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L454) | **A** | `G02`, `G03`, `G04` |
| [`eq:predictions-only`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L493) | **A** | `G03` |
| [`eq:random-start`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L505) | **A** | `G03` |
| [`eq:multiple-history`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L537) | **D** | Not a theorem on its own |
| [`eq:multiple-domain`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L546) | **A** | `G02`, `G03`, `G04` |
| [`eq:multiple-recursion`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L577) | **A** | `G03` |
| [`eq:multiple-predictions`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L592) | **A** | `G03` |
| [`eq:multiple-mean`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L601) | **A** | `G03` |
| [`eq:multiple-population-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L627) | **F** | `G01` |
| [`eq:multiple-conditional-variance`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L670) | **A** | `G02`, `G03`, `G04` |
| [`eq:multiple-conditional-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L677) | **A** | `G02`, `G03`, `G04` |
| [`eq:two-predictions`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L695) | **A** | `G03` |
| [`eq:two-mean`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L698) | **A** | `G03` |
| [`eq:two-population-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L704) | **F** | `G01` |
| [`eq:two-conditional-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L708) | **A** | `G02`, `G03`, `G04` |
| [`eq:three-predictions`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L726) | **A** | `G03` |
| [`eq:three-mean`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L729) | **A** | `G03` |
| [`eq:three-population-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L735) | **F** | `G01` |
| [`eq:three-conditional-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L739) | **A** | `G02`, `G03`, `G04` |
| [`eq:iq-scale`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L839) | **D** | Not a theorem on its own |
| [`eq:iq150-start`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L844) | **D** | Not a theorem on its own |
| [`eq:iq150-prediction`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L864) | **A** | `G18` |
| [`eq:iq150-predictions`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L870) | **A** | `G18` |
| [`eq:iq150-mean`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L882) | **A** | `G18` |
| [`eq:iq150-population-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L898) | **F** | `G01` |
| [`eq:iq150-conditional-sd`](../analyses/sequential-conditional-means/sequential_conditional_means.tex#L901) | **A** | `G18` |

### SQ-S: 7 distinct labels

| Exact source anchor | Disposition | Remaining proof task(s) |
|---|---|---|
| [`eq:seq-sim-factor`](../analyses/sequential-conditional-means/sequential_simulations.tex#L100) | **D** | Not a theorem on its own |
| [`eq:seq-sim-centre`](../analyses/sequential-conditional-means/sequential_simulations.tex#L126) | **A** | `G03`, `G04` |
| [`eq:seq-sim-population`](../analyses/sequential-conditional-means/sequential_simulations.tex#L142) | **F** | `G01` |
| [`eq:seq-sim-conditional`](../analyses/sequential-conditional-means/sequential_simulations.tex#L145) | **A** | `G03`, `G04` |
| [`eq:seq-sim-posterior-factor`](../analyses/sequential-conditional-means/sequential_simulations.tex#L167) | **P** | `G03`, `G04` |
| [`eq:seq-sim-future-vector`](../analyses/sequential-conditional-means/sequential_simulations.tex#L181) | **P** | `G03`, `G04` |
| [`eq:seq-sim-limit-sds`](../analyses/sequential-conditional-means/sequential_simulations.tex#L422) | **A** | `G22`, `G23` |

## Appendix — full AI disclosure

OpenAI ChatGPT reviewed the four specified project/reporting READMEs, identified the six linked authoritative XeLaTeX report sources, inspected their theorem/proof-bearing inputs and claim maps, compared their mathematical obligations with the existing finite/algebraic Rocq inventory and known module names, and prepared this register and backlog. ChatGPT classified proof status, assigned candidate dependencies and drafted documentation. The classifications are an assessment to be independently reviewed, **not** kernel certificates of the full report theorems, not a demonstration that the PDFs equal the TeX, and not a new proof of Gaussian laws. Some formal claims have exact finite witnesses or partial algebraic proof terms; these must not be conflated with measure-theoretic theorems. No new mathematical theorem was proved in creating this audit. The source files, referenced external results, statistical assumptions, simulation outputs and formal proofs remain subject to their separate evidence standards. Anders Hellström requested this audit.
