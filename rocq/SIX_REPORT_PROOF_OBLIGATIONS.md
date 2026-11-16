# Six-volume Rocq proof-obligation register — D042x

> **AI DISCLOSURE:** This source-audit and formalization backlog were prepared with OpenAI ChatGPT assistance. A report proof, source scan or simulation is not a Rocq kernel proof. Author/researcher/requester: **Anders Hellström**.

**Date:** November 16, 2026. **Pinned baseline:** [`5c23afcd48bd36302c0acd2bbdf75271abf06921`](https://github.com/AndersH3/composite_iq_checked_claims/commit/5c23afcd48bd36302c0acd2bbdf75271abf06921). The six authoritative XeLaTeX sources are linked from the four project/reporting READMEs. This register covers all six main/simulation volumes, their proof-bearing inputs and claim-to-evidence maps. It distinguishes the full report proposition from a previously kernel-checked **finite** or **algebraic** fragment.

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

## Appendix — full AI disclosure

OpenAI ChatGPT reviewed the four specified project/reporting READMEs, identified the six linked authoritative XeLaTeX report sources, inspected their theorem/proof-bearing inputs and claim maps, compared their mathematical obligations with the existing finite/algebraic Rocq inventory and known module names, and prepared this register and backlog. ChatGPT classified proof status, assigned candidate dependencies and drafted documentation. The classifications are an assessment to be independently reviewed, **not** kernel certificates of the full report theorems, not a demonstration that the PDFs equal the TeX, and not a new proof of Gaussian laws. Some formal claims have exact finite witnesses or partial algebraic proof terms; these must not be conflated with measure-theoretic theorems. No new mathematical theorem was proved in creating this audit. The source files, referenced external results, statistical assumptions, simulation outputs and formal proofs remain subject to their separate evidence standards. The author, researcher and requester is Anders Hellström.
