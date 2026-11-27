**Scope update (November 27, 2026):** The [eight-report mandatory proof register](EIGHT_REPORT_PROOF_OBLIGATIONS.md) and its seven linked source indices supersede the previous six-volume scope. All mathematical claims, including inline prose and numerical targets, require equivalent Rocq results; preserve this document as historical proof-mapping evidence. No full-scope completion is claimed.

> **AI disclosure — prepared with AI assistance.** This is a source-based theorem inventory and formalization-status register, not an independent validation of any Gaussian model or empirical IQ claims. The source references and proof scopes were checked against the files listed below.

# Theorems and mathematical claims actually used in the reports

> **D053–D056 kernel-verified continuation (November 17, 2026):**
> The [pinned Rocq 9.2 run](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/44153123270)
> accepted **105 additional** report-relevant theorems in three
> canonical source modules: [GaussianInnovationBounds.v](../analyses/sequential-conditional-means/rocq/GaussianInnovationBounds.v)
> (43), [GaussianBatchBalance.v](../analyses/sequential-conditional-means/rocq/GaussianBatchBalance.v)
> (30), and [GaussianFiniteHistoryPosterior.v](../analyses/sequential-conditional-means/rocq/GaussianFiniteHistoryPosterior.v)
> (32). They map to the sequential conditional-means book's general
> initial-`n` predictor formula, exact inclusive averaging, signed
> covariance-domain feasibility, conditional Schur variance, arbitrary
> finite-history sufficiency, and Gaussian posterior precision/variance
> update formulas. The existing source-ordered
> [Gaussian proof register](PROOF_REFACTOR_GAUSSIAN.md) records
> every new declaration and its exact owner. The D050–D056
> Gaussian-specific total is **292** kernel-checked declarations.
> Crucially, this does **not** prove Gaussian residual independence,
> the multivariate normal measure, or the actual measure-theoretic
> conditional expectation. This inventory and its mappings were AI-assisted.
>


> **D046x verified continuation (November 16, 2026).**
> The [159 new Rocq 9.2 kernel-checked statements](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43847174190) in
> [`ListPoolingAlgebra.v`](../library/rocq/ListPoolingAlgebra.v)
> extend `sm:pooling` (G12) to arbitrary finite lists of group summaries,
> with exact weighted ANOVA, centered cross-products and covariance.
> They also supply deterministic heterogeneous Bernoulli rate/variance
> bounds for `sm:binomial` and `sm:rare` (G08/G13).
> The 16 definitions and 159 theorems are documented in the
> [dedicated source-ordered register](PROOF_REFACTOR_LIST_POOLING.md).
> Verified inventory: **2,947 scripts, 36 modules**. The full stochastic
> distribution and interval-coverage obligations remain open; no
> empirical test-population law was proved. AI-assisted specification,
> proofs and documentation are limited to exact kernel-accepted statements.
>
> **D044x kernel-checked extension (November 16, 2026).** The
> [full six-volume obligation register](SIX_REPORT_PROOF_OBLIGATIONS.md)
> maps **111 additional** proofs: [39 three-group pooling theorems](../library/rocq/ThreeGroupPooling.v)
> including iterative within/between corrected SS, and
> [72 two-rate precision theorems](../library/rocq/TwoRatePrecision.v)
> covering rate contrasts, expectation/variance expressions and sharp
> Bernoulli variance bounds. [Rocq 9.2 kernel CI](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43819739947)
> verified **2,603 scripts in 34 modules**. These prove exact algebraic
> parts of `sm:pooling`, `sm:binomial` and `sm:rare` for formal
> rate/count expressions. They do **not** prove independent-trial sampling,
> a binomial PMF, chi-square pivot, Gaussian tails or confidence coverage.
> This mathematical documentation and proof development were AI-assisted; mathematical validity applies only to explicit Rocq propositions accepted by the pinned kernel. Neither empirical IQ assumptions nor stochastic sampling distributions are proved by these real-algebra results.
>
> **D043x kernel-checked update (November 16, 2026):** The
> [six-volume register](SIX_REPORT_PROOF_OBLIGATIONS.md) now tracks **142
> additional** substantive real-algebra theorems in four canonical modules:
> [Wilson score](../library/rocq/WilsonScoreAlgebra.v) (36),
> [sampling precision](../library/rocq/SamplingPrecision.v) (45),
> [conditional ratios](../library/rocq/ConditionalRatioStability.v) (30),
> and [pooled moments](../library/rocq/PooledMomentsAlgebra.v) (31).
> [Pinned Rocq 9.2 build](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43812796040)
> compiled the full 32-module source and checked 2,492 proof scripts on
> commit `955379823a469ff57e8eb5f2320994697c7d5ef0`.
> The new results discharge algebraic portions of `sm:wilson`, `sm:rare`,
> `sm:pooling`, Towers' conditional-rate sensitivity, and Bernoulli
> moment/precision expressions. They do **not** prove the missing binomial,
> Gaussian, chi-square or exact confidence-coverage distributional laws.



> **Update, November 16, 2026 — full six-report source audit:** The authoritative [six-volume proof-obligation register](SIX_REPORT_PROOF_OBLIGATIONS.md) covers **all three main reports and all three simulation reports**, their eleven proof-bearing TeX sources, 70 individually labelled mathematical results and 24 reusable proof-work packages. This older inventory remains the detailed **three-analytical-report history**; do not infer that its older scope or status covers simulation diagnostics, chi-square, Wilson or Clopper–Pearson theorems. A limited finite/algebraic Rocq proof must not be equated with full Gaussian/statistical coverage.


**Author:** Anders Hellström.

**Audit date:** November 14, 2026. **Original audit baseline:** `main` at merge commit `b90da09b4df1ee7ba8b502b6afe484a4046a1455` (PR #7). **Current continuation base:** `main` at merge commit `694bf832697d59ccb07f2645e711e28120bdd688` (PR #24). **Working branch:** `architecture-central-libraries-20261115` (PR #25).

The inventory is organized **by the claims in the actual report sources**, not by every theorem that happens to have been proved in Rocq. Thus the audit discriminates relevant proof work from the large general-purpose covariance library. It covers three reports and the sequential report's two included proof appendices:

- [Hoeflin/Ferguson composite-score report](../analyses/hoeflin-ferguson/composite_iq_analysis.tex).
- [Towers multiple-test admissions report](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex).
- [Sequential conditional-means report](../analyses/sequential-conditional-means/sequential_conditional_means.tex), its [foundational theorems](../analyses/sequential-conditional-means/theorem_foundations.tex), and [numerical proof certificates](../analyses/sequential-conditional-means/exact_numeric_certificates.tex).

### D041x — algebraic trivariate Schur conditions for Towers and Sequential covariance models

The shared `TrivariateSchur.v` proves 27 reusable 3×3 real covariance-determinant,
residual-product, singularity and conditional-covariance inequality propositions,
using Stdlib real algebra. The report-owned `ThreeTestSchur.v` instantiates
27 propositions for each of AB|C, AC|B and BC|A in the Towers multiple-test
analysis (81 specialized claims). The central equation is
`(u w-q²)(v w-r²)-(p w-qr)²=w det(Sigma)`; whenever `w>0` it
characterizes strict and weak Schur residual bounds by the determinant sign.

**Theorem mapping:** Sequential foundational `thm:moments` (covariance
matrix algebra and the scalar residual formula), `thm:spectral` (necessary
positive-semidefinite inequalities), `thm:gaussian` (covariance identities
used in the cited Gaussian argument but not its distributional assertion);
Towers pairwise-dependence and third-test conditioning discussion. These
claims remain **algebraic implications under explicit real hypotheses**; no
Gaussian characteristic-function uniqueness, conditional probability law,
trivariate tail quadrature or empirical model validation is established.
Only the final pinned Rocq kernel check can label these statements K.

### D039x — exact two-stratum association decomposition for Towers

The Towers report's dependence and union claims motivate the general finite
2×2 selection identity
`t_selected * t_other * pooled_association =
(t_selected+t_other) * within_component + between_component`.
The 44 new report-independent theorems under
[`TwoStratumAssociation.v`](../library/rocq/TwoStratumAssociation.v)
prove this polynomial identity, two conditional marginal-rate gap formulas,
sign equivalences and criteria for positive or negative association reversal.

A further 60 new [Towers-specific bridge theorems](../analyses/towers-multiple-test-admissions/rocq/ThreeTestSelectionDecomposition.v)
specialize the decomposition to AB given C, AC given B and BC given A,
using the actual eight Boolean admission cells. They identify the pooled
association with existing `Admissions` / `ThreeTestPairBridge` proofs,
prove the complementary selection groups have total probability one, and
derive exact adjusted sign and Simpson-reversal criteria.

The mathematical boundary remains finite weighted Boolean admissions
and algebra. Neither trivariate Gaussian regression nor numerical normal
tail certificates, actual test correlations, or population admissions rates
are established by these theorems. Treat the new statements as kernel
proved only after Rocq 9.2 accepts the exact final source head.

### D040x — formal sharp reversal thresholds and conditional independence

The 50 generic [`TwoStratumReversal.v`](../library/rocq/TwoStratumReversal.v)
theorems give necessary-and-sufficient criteria for the sign of pooled
two-test association, expressed as a comparison between between-group
selection association and the negative weighted within-stratum term.
They also characterize when conditional independence in both groups
implies pooled independence, and when at least one route's selected and
nonselected admission rates must agree.

The 75 [`ThreeTestReversalCriteria.v`](../analyses/towers-multiple-test-admissions/rocq/ThreeTestReversalCriteria.v)
theorems specialize these statements to AB given C, AC given B, and
BC given A. They formally connect the tests' exact eight-atom
cross-product determinants to the population-level association and
give necessary selection-gap signs for positive and negative
Simpson-style reversal. Premises explicitly require positive selected
and other-group masses and, where relevant, strict local
association signs; the conclusions do not presume Gaussianity.

These are 125 additional *finite-model* theorem statements. Rocq 9.2
kernel acceptance at the exact final source revision is required before
they may be called proved. This work neither validates the
reports' population-IQ distribution assumptions nor certifies
continuous Gaussian tail probabilities.

## D047x — four-test covariance contractions and finite-list bridges (169 proof scripts)

**Author:** Anders Hellström. **AI disclosure:** OpenAI ChatGPT assisted statement design, polynomial expansion, proof scripting and this register. Kernel compilation at an exact source revision—not text or code generation—determines proof status.

The new shared [`FourContrastCovariance.v`](../library/rocq/FourContrastCovariance.v) has **169 explicit theorem proofs and 3 definitions**. Fourteen general matrix-bilinearity/quadratic identities and 136 exact variance/covariance evaluations of 16 meaningful score contrasts establish the symbolic contraction algebra. The remaining 19 proofs establish actual finite-list covariance linearity, four-test sample covariance and variance matrix bridges, nonnegative empirical covariance quadratic forms under nonnegative sample weights and positive mass, six applied composite-score formulas, and four-score sample mean linearity.

For the shared report proposition `pf:moments` (G01) this provides a direct **deterministic four-score finite-sample analogue** of `Var(w^T X)=w^T Sigma w` and `E(w^T X)=w^T mu`, plus the constructive positive-semidefinite sample covariance result. The D046x pooling results underpin the moment calculations (G12). The 136 evaluations are *related specializations* of one symmetric polynomial, not 136 independent scientific discoveries.

**Checked inventory when validated at the final source head:** 3,116 proof scripts, 3,102 public theorem/lemma/example statements, 3,414 documented declarations, across 37 modules. The symbolic ten-entry covariance form does **not** assert feasibility for arbitrary real matrix inputs: PSD is proved only for matrices constructed from nonnegative-weight finite samples. The report's general random-variable expectation theory, Gaussian conditional distributions, normal tails, chi-square pivots, independent binomial laws, interval coverage, Monte Carlo accuracy, and empirical IQ-model assumptions remain outside these finite/algebraic statements.


## Verification levels (do not conflate)

**K — Kernel-checked at stated mathematical scope:** a named Rocq theorem proves the displayed finite/algebraic proposition, with its explicit hypotheses. **A — Algebraic consequence formalized:** the report's rational formula is checked, but the stochastic Gaussian premise from which the report derives it is **not** proved. **P — Report proof / cited established theorem only:** the typeset report gives a mathematical proof or reference, but no corresponding general Rocq kernel theorem has been supplied. **E — Empirical or numerical/modeling claim:** its correctness requires numerical/error-certified evaluation or assumptions about a real test population. A claim labelled P or E is not converted to K merely by a successful Rocq build.

The `SequentialReport.v` module now has **seven definitions and 37 Rocq 9.2 kernel-checked real-algebra and natural-induction theorems**. Both [Rocq push CI](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43627749197) and [Rocq pull-request CI](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43627753031) passed on commit `a6d3135c`. This verifies the stated arithmetic and finite recursion, **not** the Gaussian conditional-law claims, which remain P.

## I. Sequential conditional-means report — explicitly stated results

| Report label | Theorem actually used | Rocq implementation / reuse | Verification boundary |
|---|---|---|---|
| `thm:moments` | Linear expectation, bilinear covariance, variance of a linear composite, variance-zero iff constant a.s. | `FiniteMoments.v`: `expectation_of_general_weighted_sum`, `covariance_of_general_weighted_sums`, `variance_of_general_weighted_sum`, `zero_variance_is_constant_on_positive_mass`. New `FiniteConditionalCovariance.v` extends these to exact bilinear finite centered covariance numerators, affine score transformation, polarization and variance specialization using explicit weighted occurrences. | **K for normalized finite nonnegative measures**; general measure-theoretic version **P** |
| `thm:conditional` | Existence/uniqueness of conditional expectation, tower property, pull-out and law of total variance | `FiniteUnion.v` and `FiniteBridge.v` provide event conditioning; new `FiniteTwoCellProjection.v` proves the exact weighted-score **two-cell conditional-mean tower, residual orthogonality, unique least-squares projection, and full finite law of total variance** for actual filtered outcome lists with explicit positive-mass assumptions. New `FiniteNestedProjection.v` constructs a sequential **four-cell refinement** from two Boolean observations and checks pointwise finite projection idempotence and the **tower**, residual orthogonality to all four-cell functions, risk monotonicity under additional information and nested law of total variance. New `FiniteConditionalCovariance.v` additionally proves the **finite pull-out property**, pointwise affine/linear two-cell conditioning and the full **law of total covariance**, decomposed into within-cell covariance and between-cell conditional-mean products. `FiniteConditionalResidual.v` additionally identifies the finite **fitted covariance with the between-cell covariance** and the finite **residual covariance with within-cell covariance**, proves all fitted/residual mixed centered covariance terms vanish, establishes finite variance explained and residual-risk bounds, and proves uniqueness of the best two-cell prediction pair under strictly positive masses. **No** general `L¹` conditional-expectation or general sigma-algebra formalization. | **K for the explicit finite Boolean-partition analogs only; P for general measure-theoretic conditional expectation** |
| `thm:spectral` | Spectral PSD criterion and Gaussian realization of PSD covariances | `EquicorrelationSpectral.v` proves the two rank-one eigenvalue conditions on feasible summaries; `EquicorrelationVectors.v` now proves **finite-list Cauchy–Schwarz**, Cauchy feasibility, and the necessary-and-sufficient PSD and PD conditions for **every real list of fixed length n>=2**, with concrete common/contrast witnesses. `FiniteMoments.v` supplies general finite covariance PSD. General spectral theorem and Gaussian realization absent. | **K for actual finite-dimensional equicorrelation quadratic forms and PSD/PD iff; P for general spectral theorem and Gaussian realization** |
| `thm:gaussian` | Gaussian affine transformation, covariance identification, independent blocks iff zero cross covariance | No Gaussian law or Gaussian-block independence formalization | **P** |
| `thm:regression` | Gaussian block regression mean `mu_U+C B^{-1}(v-mu_V)`, Schur conditional covariance | `FiniteMoments.v` proves finite covariance Schur identities; new `TwoObservationSchur.v` checks the **general invertible symmetric two-observation covariance-block inverse, unique best pair of regression coefficients, positive-definite quadratic risk, Schur complement, and exact nonnegative/strict second-observation information gain** with no equicorrelation assumption; `EquicorrelationInverseVectors.v` additionally proves the **unique minimum-risk common linear prediction coefficient**, algebraic residual orthogonality, and finite Schur action identities using actual real score lists. These establish the deterministic regression normal equations, **not** the Gaussian conditional distribution. | **K/A for exact two-observation Schur covariance, finite conditional projection and optimal linear-prediction algebra; P for Gaussian conditional-mean law** |
| `lem:continuous-version` | Equality of continuous conditional-mean versions everywhere under full-support Gaussian conditioning | No topology/continuous-version probability kernel theorem | **P** |
| `thm:induction` | Mathematical induction on natural numbers | Rocq/Stdlib's built-in `nat_ind`; no custom induction scheme needed | **K (Stdlib)** |
| `prop:domain` | Equicorrelation matrix PSD exactly when `-1/k <= c <= 1`; all finite sizes require `0 <= c <= 1` | `EquicorrelationSpectral.v` supplies the exact interval and scalar spectrum; `EquicorrelationVectors.v` proves PSD and PD iff for **all concrete real lists** at each dimension n>=2, using a kernel-checked finite Cauchy–Schwarz inequality and sharp common/contrast witnesses. All-length intersection and Gaussian realization are separate. | **K for the complete finite-vector equicorrelation PSD/PD criterion**; **P for Gaussian realization and general matrix spectral theorem** |
| `thm:equicorrelated-conditioning` | Gaussian history-to-prediction coefficient `c/d_n` and residual variance `(1-c)(1+nc)/d_n`, including singular joint boundary | `sequential_denominator_add`, `sequential_residual_variance_identity`, `sequential_residual_covariance_identity` | **A for regression arithmetic**, **P for Gaussian conditional law** |
| `thm:single-start` | Every recursively predicted future score equals `ca`; average includes `a` and equals `(1+kc)a/(1+k)` | `sequential_prediction_single_start`, `sequential_mean_single_start`, `sequential_recursive_history_sum_closed_form`, `sequential_recursive_single_start_predictions_constant` | **A** for the complete finite-history induction and mean, **P** for the Gaussian conditional-mean model itself |
| `prop:population-sd` | Equal-covariance population average variance `[1+kc]/(k+1)` and nonnegative square-root SD | `Hoeflin.equal_weight_variance`, `FiniteMoments.equal_weight_variance_from_finite_covariances`, `sequential_population_variance_matches_composite` | **K for finite covariance structure, A for formula matching**; population Gaussian assumptions unnecessary |
| `prop:conditional-sd` | One observed score: conditional mean `lambda_k a`, variance `lambda_k(1-lambda_k)`, SD via square root | `sequential_conditional_variance_one_start`, `sequential_conditional_variance_lambda_identity` | **A** for identity, **P** for conditional distribution |
| `thm:multiple-mean` | `r` equal initial scores produce prediction `rca/d_r`; inclusive mean `r d_N a/(N d_r)` | `sequential_prediction_recursive_fixed_point`, `sequential_inclusive_mean_closed_form`, `sequential_recursive_prediction_constant`, `sequential_recursive_inclusive_mean_closed_form` | **A** for exact rational identities and complete finite-history induction; Gaussian conditional expectation remains **P** |
| `thm:multiple-sd` | Population variance `d_N/N`; conditional variance `k(1-c)d_N/(N² d_r)` | `sequential_population_variance_matches_composite`, `sequential_conditional_variance_from_pairings`, finite covariance quadratic form | **K/A** for unconditioned finite variance and residual algebra, **P** for Gaussian conditional covariance |
| `cor:two-starts` | Predictions, inclusive mean, population and conditional SD for `r=2` | `sequential_prediction_two_starts`, `sequential_mean_two_starts`; variance formulas are specializations of generic case | **A**, including only the arithmetic content; not a Gaussian-SD proof |
| `cor:three-starts` | Analogous formulas for `r=3` | `sequential_prediction_three_starts`, `sequential_mean_three_starts` | **A**, including only arithmetic content |
| `prop:multiple-boundaries` | `c=1`, `c=0`, singular lower boundary and `k=0`; compatible histories | `sequential_prediction_independence_limit`, `sequential_mean_independence_limit`, `sequential_mean_perfect_correlation_limit`, `sequential_conditional_variance_perfect_correlation`, `sequential_conditional_variance_singular_boundary` | **A** for algebraic boundaries, **P** for singular Gaussian support/versions |
| `cor:iq-reporting` | Standardization of IQ 150 and affine re-scaling of predictions and SD | `sequential_iq_start_standardized`, `sequential_iq_prediction_exact`, `sequential_iq_mean_exact`, `sequential_iq_population_variance_exact`, `sequential_iq_conditional_variance_exact` | **A** for exact rational conversion; actual Gaussian conditional distribution not constructed |
| `prop:counterexample` | Equal marginal distributions, standardized variances and zero correlation can conceal different conditional means and recursive averages at a positive-mass starting score | `ReportCounterexample.v` supplies a different exact **rational finite witness**, with both marginals identical, E[X]=E[Y]=0, Var(X)=Var(Y)=1, Cov(X,Y)=0, P(X=0)=1/2, but E[Y|X=0]=-1 versus 0; the inclusive averages are -1/2 and 0 | **K — finite positive-event counterexample**, which refutes distribution-free conditional-mean inference but does not prove Gaussian regression |
| `cor:exact-iq-values` | Exact fractions `100+50r(3N+2)/(N(3r+2))`, `45(3N+2)/N`, `90k(3N+2)/(N²(3r+2))` | `sequential_iq_mean_exact`, `sequential_iq_population_variance_exact`, `sequential_iq_conditional_variance_exact` | **A** for the exact fraction formulas; the probabilistic interpretation has the above prerequisites |
| `lem:rounding` | Rigorous strict integer-grid nearest-decimal tests for a rational mean and square-root SD, including tie exclusion | `ReportRounding.v`: `report_strict_rounding_interval_unique`, `report_rational_certificate_sound`, `report_sqrt_variance_certificate_sound`; nine `report_iq150_certificate_r*_k*` equalities check all 45 source integer gaps | **K for real interval/inequality lemmas and integer table certificates**; the general integer-to-real cast pipeline is not packaged as a single Rocq theorem, and Gaussian-law interpretation remains **P** |

### D035x — sequential parameter sensitivity and explained variance

The specialized [`SequentialSensitivity.v`](../analyses/sequential-conditional-means/rocq/SequentialSensitivity.v)
adds **55 explicitly documented mathematical statements** tied to the report's
`prop:domain`, `thm:equicorrelated-conditioning`, `thm:multiple-mean`,
`thm:multiple-sd`, and population/conditional-SD formulas. These are
source-level proof claims until the final pinned kernel check succeeds.

| Report dependency | Exact additional mathematical results | Trust boundary |
|---|---|---|
| `prop:domain`, denominator `d_n` | 10 shared-denominator affine, count/correlation-gap, positive/upper-bound and monotonicity identities | Finite battery algebra; not covariance realizability of a Gaussian random vector |
| `thm:equicorrelated-conditioning` and prediction weight | 14 proofs of regression coefficient scaling, perfect/independent boundaries, sharp loss fraction, strict range, exact count/correlation sensitivity and monotonicity | Deterministic assumed regression coefficients; not Gaussian conditional expectation |
| `prop:population-sd`, `thm:multiple-sd` | 12 proofs of population common/idiosyncratic variance, strict size/correlation ordering and exact finite-count sensitivity | Algebraic covariance and quadratic variance; not a certified Gaussian SD distribution |
| `thm:multiple-sd` and explained variance | 8 identities/strict inequalities for residual risk, uncorrelated boundary, exact explained fraction and total/residual decomposition | Algebraic Schur residual expression; no Gaussian conditioning or empirical calibration |
| `thm:multiple-mean` | 11 exact inclusive-mean affine, shrinkage, bounds, and finite correlation/future-count difference claims | Assuming the model's prediction formula, not establishing that formula probabilistically |

### Additional consequential labelled sequential formulas

| Report equation(s) | Mathematical role | Checked algebra / remaining gap |
|---|---|---|
| `eq:inverse`, `eq:coefficient` | Inverse of equicorrelation block and regression coefficient | `EquicorrelationSpectral.v` proves scalar inverse compositions; `EquicorrelationInverseVectors.v` proves **both full finite-list inverse compositions**, the exact inverse coordinate sum, explicit inverse precision form and common/contrast reciprocal eigenspaces. These precisely represent the n-by-n equicorrelation matrix acting on any real list of length n; no general-purpose indexed matrix library theorem or Gaussian regression law is claimed |
| `eq:recursion`, `eq:all-predictions`, `eq:answer`, `eq:multiple-recursion`, `eq:multiple-predictions`, `eq:multiple-mean` | Recursion and inclusive means | The complete natural-number induction is **kernel-checked** in `sequential_recursive_history_sum_closed_form` and `sequential_recursive_prediction_constant`; Gaussian conditional-law justification remains open |
| `eq:population-variance`, `eq:multiple-population-sd` | General finite average variance | `FiniteMoments.v`, `Hoeflin.v`, and `SequentialReport.v` |
| `eq:conditional-variance`, `eq:multiple-conditional-variance` | Conditional covariance of Gaussian scores | Rational residual simplification and concrete Schur-block matrix action/dot-product now checked; **probabilistic Gaussian conditional-covariance theorem open** |
| `eq:iq150-mean`, `eq:iq150-population-sd`, `eq:iq150-conditional-sd` | Reporting-scale conversion | The rational mean and **squared SD** formulas are checked; sqrt as a nonnegative SD still relies on report's interpretation |
| `eq:fixed-sd` | A fixed recursion output is deterministic; its SD is zero | Constant variance is already a finite-moment identity, not the conditional SD of the random test-score mean |

## II. Hoeflin/Ferguson composite-score report

The report gives labelled equations rather than a separate list of theorem environments. These are the **theorem-level mathematical identities used**, with the essential probability/model boundaries.

| Report equation | Claim | Rocq evidence and status |
|---|---|---|
| `eq:variance-sum` | `Var(X+Y)=Var(X)+Var(Y)+2Cov(X,Y)` | **K finite:** `FiniteMoments.variance_of_two_weighted_scores`, bilinearity and symmetry |
| `eq:standardize` | `z_i=(x_i-mu_i)/sigma_i` | A definition, assuming `sigma_i>0`; not a standalone stochastic theorem |
| `eq:weighted-variance` | `Var(wᵀZ)=wᵀRw` | **K finite:** `FiniteMoments.covariance_matrix_quadratic_form_is_variance` and `variance_of_general_weighted_sum`; `TwoObservationSchur.cov2_quad_completed_square` and `cov2_quad_positive_semidefinite` cover the general 2-by-2 quadratic case |
| `eq:average-correlation`, `eq:mean-variance` | Equal-weight variance depends on pair-average correlation | **K finite:** `FiniteMoments.equal_weight_variance_from_finite_covariances`; `Hoeflin.equal_weight_variance` |
| `eq:weighted-composite`, `eq:equal-composite` | Unit-variance standardization when composite variance is positive | **K finite/algebraic:** `Hoeflin.normalized_variance_is_one`; requires matched population parameters |
| `eq:reporting-scale`, `eq:iq-composite`, `eq:worked-example` | Affine IQ reporting scale and a worked composite | **K/A:** `Hoeflin.equal_sd_composite_scale` and `standardized_160_sd16`; any population interpretation is external |
| `eq:quantile`, `eq:threshold` | Standard-normal one-in-a-million quantile and mean cutoff | **E:** numeric inverse-normal evaluation is not a Rocq normal-CDF theorem |
| `eq:limit` | Limit as battery size increases at fixed average correlation | **K/A** for variance convergence bound via `Hoeflin.fixed_correlation_variance_epsilon_bound`; sqrt limit needs standard continuity assumptions |
| `eq:factor-model`, `eq:factor-reliability` | Hypothetical common-factor Gaussian construction and reliability formula | **K/A** for the scalar reliability algebra in `Hoeflin.v`; **P** for Gaussian stochastic construction |
| `eq:latent-mean`, `eq:latent-variance` | Posterior Gaussian mean and variance of the latent factor | **A** for `Hoeflin.latent_posterior_variance` and algebra; **P** for Gaussian conditional expectation and variance |

## III. Towers multiple-test admissions report

| Report equation | Claim | Rocq evidence and status |
|---|---|---|
| `eq:model`, `eq:cutoffs` | Joint bivariate Gaussian assumption and marginal normal quantiles | **P/E**; model definition/quantile input, not implied by knowing the correlation. `TwoObservationSchur.v` gives deterministic bivariate PSD, determinant and inverse algebra, **not** the bivariate Gaussian tail integral |
| `eq:joint` | Bivariate Gaussian joint exceedance integral | **P**; no continuous Gaussian integration proof in the current Rocq modules |
| `eq:union` | `P(A union B)=p_A+p_B-J` | **K:** `Admissions.v`, `FiniteUnion.two_event_union_probability` |
| `eq:conditionals` | `P(B|A)=J/p_A`, `P(A|B)=J/p_B` | **K:** `Admissions.conditional_B_numerator` and `conditional_A_numerator`; positive denominators required |
| `eq:phi` | Binary-indicator phi/covariance relation, distinct from underlying continuous Pearson `rho` | **K** for indicator covariance numerator via `Admissions.binary_indicator_covariance_numerator` and `FiniteBridge.finite_event_indicator_covariance`; normalized phi requires nonzero marginal variances |
| `eq:bounds` | Finite union probability between max marginal and min(1,sum) | **K:** `FiniteUnion.arbitrary_union_bound`, `normalized_arbitrary_union_at_most_one` |
| `eq:equal-results`, `eq:mixed-joint`, `eq:mixed-conditionals`, `eq:mixed-remainder`, `eq:union-denominator` | Published bivariate-normal numeric cases and different denominators | **K** for algebra conditional on an asserted joint mass; **E** for numeric Gaussian tail integrals and rounding |
| `eq:rarity`, `eq:calibration` | Normal rarity-equivalent conversion and inverse cutoff calibration | **E**, requires normal quantile and certified root-finding, not finite event algebra |
| `eq:grid` | Legacy finite-grid Gaussian density ratio | Generic finite sums are checked in `FiniteSum.v`; the particular quadrature truncation/error is **E** |
| `eq:rho-integral` | Bivariate normal overlap as integral of density with respect to correlation | **P**, requires differentiability/integration of Gaussian law and is not currently kernel-checked |

### D036x — three-route admissions (Towers multiple-test extension)

The Towers-specific [`ThreeTestAdmissions.v`](../analyses/towers-multiple-test-admissions/rocq/ThreeTestAdmissions.v)
uses **eight exhaustive Boolean outcomes** and the canonical `FiniteSum` /
`FiniteUnion` probability engines. Its 55 named proof scripts establish
three-event exact-overlap and count formulas for the logical generalization
of `eq:union`, `eq:conditionals` and `eq:bounds`. The essential outcomes
include exact probability of exactly one/two/three admitted routes,
three-way inclusion-exclusion, the triple Fréchet bound
`P(A∩B∩C) ≥ P(A)+P(B)+P(C)−2`, and first/second-order Bonferroni
inequalities. All results refer to a **finite, normalized, nonnegative
sample of the eight Boolean patterns**. They need the final pinned Rocq
9.2 kernel CI before being labelled checked and do not verify a trivariate
normal integral or empirical psychometric parameters.

### D037x — certified pairwise marginalization of the three-test model

The Towers report's two-test formulas are connected to the three-test model
using the **three certified** `TwoEventModel` projections
`pair_AB3`, `pair_AC3` and `pair_BC3` from
[`ThreeTestPairBridge.v`](../analyses/towers-multiple-test-admissions/rocq/ThreeTestPairBridge.v).
Each projection sums out the omitted Boolean admission outcome while retaining
eight-atom nonnegativity and unit total mass. The **84 report-specific
bridge theorems** tie pairwise marginal success, intersection, exclusive
success, conditional rates, binary-indicator variance/covariance, odds ratio,
phi correlation, independence criteria, Fréchet lower bounds and positivity
conditions to the original three-route probabilities. Nearly all pairwise
properties are delegated to the existing checked `Admissions.v` laws;
there are no duplicate four-cell event engines or Gaussian assumptions.

Only the pinned Rocq 9.2 kernel can certify these proofs. Their scope is
finite normalized event algebra, not Gaussian joint tails, Gaussian
conditioning or measured psychometric correlations.

### D038x — selection and Simpson reversal for three admission tests

The Towers report's admitted-by-any-test and overlap formulas depend
on the interaction among multiple test results. The new
[`ThreeTestConditionalStrata.v`](../analyses/towers-multiple-test-admissions/rocq/ThreeTestConditionalStrata.v)
derives six explicit conditional two-test models, distinguishing
AB|C and AB|not-C, AC|B and AC|not-B, BC|A and BC|not-A.
Conditional masses are obtained by dividing the relevant four
raw three-test atoms by the **strictly positive** selected stratum
probability. This is a *finite* conditional probability model, not
a claim of continuous Gaussian regular conditional distributions.

Its 15 generic and 102 specialized theorems connect
conditional union/marginal/exclusive rates, association sign,
raw cross-product independence, conditional odds ratios, and
Fréchet bounds to the original eight-event model. The other nine
theorems verify an exact **Simpson's paradox** witness with
pooled `P(A) = P(B) = 1/2` and `P(A ∩ B) = 33/100`, and
negative AB association separately in C-positive and C-negative
strata. Thus naïvely transporting pairwise dependence across
selection strata is mathematically invalid even for fully specified
finite contingency tables. No report source's normal-tail integrals,
empirical IQ correlations, or institutional test-admissions
parameters are thereby certified. All claims require pinned Rocq
9.2 compilation on the final source.

## IV. Proof-development priorities based on report dependence

1. **Highest impact, genuinely missing:** Gaussian regression, conditional expectation (with regular conditional laws and continuous versions), and equicorrelation positive-semidefinite/spectral construction. The current Schur covariance theorems do **not** establish these stochastic claims.
2. **Checked in the maintained finite/reals infrastructure:** complete finite-history induction, two/three-start closed-form means, residual variance and exact IQ arithmetic. `SequentialReport.v` proves **37** real-algebra and induction statements, conditioned on the stated model inputs. General Gaussian regression and conditional probability laws remain open.
3. **Numerical certification:** the generic real strict-rounding criterion and nine IQ-table integer certificate rows are formalized in `ReportRounding.v`; a fully composed integer-cast end-to-end certificate proof and certified bivariate-normal tail/quantile error bounds remain open. Existing Python/SciPy regression tests do not constitute Rocq proofs of continuous probability integrals.
4. **Finite-model counterexample: complete at finite scope.** `ReportCounterexample.v` supplies two explicitly enumerated rational probability couplings with identical marginals and covariance but distinct conditional means and recursive averages at a positive-probability event. Remaining general Gaussian regression remains a separate open theorem.

The table is a scope audit: it intentionally does **not** claim that every source theorem has already been formalized. Existing checked results retain their exact finite-model hypotheses; a well-documented report proof or citation is not automatically a kernel proof.


### Continuation — equicorrelation matrix-algebra dependency (November 14, 2026)

The new `EquicorrelationSpectral.v` contains 23 explicitly scoped real-algebra theorems. Its principal contributions are a necessary-and-sufficient positive semidefinite/positive definite criterion for the rank-one quadratic form over **Cauchy-feasible aggregate energy and coordinate sums**, the strict/semidefinite eigenvalue domain and negative witnesses, an explicit inverse acting on each coordinate and total, and Schur residual energy positivity. The proof reuses `SequentialReport.sequential_d`, its positivity theorem, and established residual-covariance simplification. Finite-vector feasibility is now established in `EquicorrelationVectors.v` by an exact Cauchy–Schwarz theorem, with the resulting sharp PSD and PD criteria and a concrete matrix-action dot-product identity. A general spectral decomposition, Gaussian law and conditional expectation remain **not formalized**. **The kernel status of these new additions is determined by pinned Rocq CI, not by this prose.**



### Continuation — finite real-vector equicorrelation bridge

`EquicorrelationVectors.v` adds 34 fully documented Rocq statements over actual finite lists of real score coordinates. These include concrete Cauchy–Schwarz against the all-ones vector, mean-centered energy decomposition, zero and positive energy support equivalences, the necessity/sufficiency PSD and strict PD criteria at every fixed length n>=2, and Schur-form nonnegativity for true score lists. It reuses Rocq Stdlib.List, `FiniteSum`, and the previous `EquicorrelationSpectral` rank-one formulas. Unlike the prior feasible-summary-only theorem, the new finite-vector PSD/PD iff results explicitly quantify over all dimension-n lists and prove the aggregate feasibility premise. Three additional results establish the literal action-dot-product identity, zero-sum vector eigenspace, and strict positive-definiteness nullspace. This **does not establish Gaussian distribution realization, general spectral theorem, measure-theoretic conditioning, or actual IQ calibration**. Status must be read from pinned Rocq CI rather than assumed from source presence.



### Continuation: concrete inverse matrix and best linear prediction

The `EquicorrelationInverseVectors.v` module proves 26 additional finite-dimensional theorem statements, including both true-list inverse identities, finite quadratic `yᵀC⁻¹y`, exact mean/contrast decomposition, and the **unique** equal-weight least-squares prediction coefficient `c / d_r(c)` with its Schur residual variance and observed-coordinate covariance orthogonality. It also proves the Schur action on finite lists and its direct dot-product PSD interpretation. These results establish the formulas as matrix and deterministic least-squares consequences; the Gaussian law and conditional-expectation interpretation remain explicitly **unproved**. See pinned Rocq 9.2 CI for kernel evidence.


### Finite conditional-expectation and variance continuation

`FiniteTwoCellProjection.v` contains 26 thoroughly documented theorem declarations for an arbitrary finite weighted sample and one observable Boolean partition. It proves the exact conditional-cell weighted means, tower expectation property, zero residual expectation, orthogonality to **every two-cell-measurable score**, unique positive-mass least-squares optimality, an occurrence-preserving global-risk identity, and the exact **within-plus-between law of total variance**, implying the explained-variance inequality. All proofs share `FiniteSum.finite_sum`, Boolean `Stdlib.List.filter`, generic nonnegative-square and filter partition laws. The finite-outcome results do **not** construct general measure-theoretic `L¹` conditional expectation or any Gaussian random vector. This report inventory remains an algebraically scoped source map, not a population-psychometric validation.


### Continuation: sequential finite conditional projection and information refinement

The 29 proposed theorem scripts in `FiniteNestedProjection.v` extend the report's `thm:conditional` finite-outcome bridge to *nested* observations. For Boolean events `p` and `q`, they establish occurrence-preserving four-cell partition sums, idempotence of the two-cell operator, equality of a coarse projection of the fine predictor to the original coarse predictor at every outcome, finite tower expectation, orthogonality to arbitrary four-cell measurable functions, exact four-cell least-squares optimality, and the risk identity `coarse risk = refined risk + four nonnegative weighted squared changes in conditional means`. They also derive the nested total-variance decomposition and show that observing `q` cannot increase optimal prediction risk. Nonzero masses and strict positive masses are explicit where needed. The results remain finite weighted-list identities and **do not** prove general `L¹` conditional expectation, existence of continuous regular conditional laws, Gaussian conditioning, or any empirical psychometric premise. The Rocq 9.2 kernel must validate the final statements before their status is claimed checked.


### New continuation: finite conditional covariance and polarization

The 31 theorem scripts in `FiniteConditionalCovariance.v` formalize the **bilinear** counterpart to the previously verified conditional variance laws. Weighted finite moments have linear/affine means and pointwise two-cell predictors, the exact finite conditional **pull-out identity**, cross-loss symmetry, polarization into centered covariance and variance, covariance bilinearity, and **total centered covariance = within-cell centered covariance + between-cell mean-shift covariance**. The covariance decomposition uses actual Boolean-filtered outcome lists and explicitly nonzero cell masses. Its same-score specialization is the previous finite law of total variance. Only unnormalized finite weighted covariance numerators are proved; to interpret the expressions as probability moments, the weight function must be nonnegative and normalized. The module **does not** construct a sigma-algebra, general `L¹` conditional expectation or a Gaussian conditional distribution. Rocq kernel CI, not this inventory, establishes proof validity.


### D024x finite residual regression covariance and projection identity

The 30 theorem scripts in `FiniteConditionalResidual.v` extend the finite `thm:moments`, `thm:conditional` and regression-normal-equation analogs with exact residual-vs-fitted cross-orthogonality, zero conditional residual mean, fitted-score tower, support-constant covariance zero, uniqueness of the least-squares two-cell prediction pair, and **total centered covariance = covariance of the two fitted score functions + covariance of their two residual functions**. They further identify fitted covariance with the **between-cell conditional-mean covariance** and residual covariance with the **within-cell covariance**, which is a finite version of the conditional-regression law of total covariance. Nonnegative individual observation weights are explicit for order/variance reduction. All identities preserve finite-list multiplicities and are deterministic conditional-mean algebra, *not* a formal construction of Gaussian random variables, Gaussian conditional covariance matrices, arbitrary L¹ conditional expectation or a proof that the composite-IQ reports' empirical assumptions are correct. The pinned Rocq 9.2 kernel must verify these proof scripts independently of the claims made here.


### D025x — general two-observation block regression and conditional Schur algebra

`TwoObservationSchur.v` introduces 33 documented proof scripts for the exact symmetric 2×2 covariance block appearing in the reports' `thm:regression` and matrix quadratic `thm:moments` claims, as well as the covariance input to Towers' bivariate Gaussian admissions model. The intended results establish the fully explicit inverse coefficients, both normal equations and their uniqueness; additivity and scaling of target-covariance vectors; full covariance quadratic completion with positive-semidefinite and strict-positive-definite consequences; a completed-square identity for the **entire two-predictor least-squares risk**, its global minimum and unique minimizing coefficients; exact Schur residual variance; and nonnegative Schur complement from positivity of the **full three-coordinate covariance quadratic**. The increment from observing a second score is the exact partial-covariance square `(a*v-c*u)^2/(a*(a*b-c^2))`; its vanishing is equivalent to `a*v=c*u` and strict inequality implies strict risk improvement. The affine predictor also respects observed-score translations and target IQ rescaling. This general two-observation algebra does **not** assume equicorrelation, unlike the specialized sequential-report block. Its connection with conditional Gaussian **distributions** remains at algebraic level A: it does not prove the existence of a Gaussian vector, continuity of a regular conditional law, normal CDF integrals or empirical test-score assumptions. Positive minors and invertibility are explicit. Status of each proof is determined by the Rocq 9.2 kernel, not this inventory.

---

### Historical AI provenance before D027x

This inventory was researched, extracted, organized, and drafted by OpenAI's AI assistant using the connected GitHub repository. The assistant read the three primary XeLaTeX reports, two sequential-report appendices, existing Rocq theorem modules, compilation workflow, and proof-refactor register. It generated the 37-theorem and seven-definition `SequentialReport.v` algebraic and natural-induction formalization and mapped individual report labels to named proof declarations. Where a theorem involves Gaussian laws, measure-theoretic conditional expectations, matrix spectral properties, inverse-normal calculations, or floating-point error bounds not represented in Rocq, the inventory explicitly says so. The assistant also formalized strict rounding intervals and nine IQ-150 exact integer certificate rows in `ReportRounding.v`, and supplied an alternative rational finite countermodel of `prop:counterexample` in `ReportCounterexample.v`, while preserving the explicit boundary between arithmetic and Gaussian/probabilistic interpretations. Subsequent assistance also produced 23 Rocq-checked algebraic proofs of the feasible-summary equicorrelation PSD/PD conditions, inverse action, and Schur residual formulas, and updated the complete register and build gate. The assistant subsequently added 34 finite-vector theorem scripts, including Rocq-checked Cauchy–Schwarz and sharp equicorrelation PSD/PD criteria, matrix-action dot-product semantics, and nullspace results. The assistant did not independently validate the empirical applicability of any IQ model or change any evidence artifacts. The AI assistant subsequently formalized 26 additional finite-list matrix inverse, regression optimality, residual orthogonality, precision quadratic and Schur action statements; these are deterministic statements and are not a formalized Gaussian conditional law. The assistant additionally formalized finite weighted two-cell conditional-mean projection, tower, residual orthogonality, optimality and law-of-total-variance results, updating source references with the restricted finite-outcome scope. The assistant subsequently prepared a further 29 nested finite conditional projection theorem statements and proof scripts, extending the finite tower and total variance to sequential observations without assuming any Gaussian law. OpenAI assistance additionally prepared 31 finite conditional covariance, polarization, affine-prediction and pull-out proof scripts mapped to the report's `thm:moments` and `thm:conditional`; no empirical model validation or Gaussian conditional law is implied. AI assistance also supplied the 30 finite residual/fitted covariance theorem statements and proof scripts, updating their report mappings and preserving the distinction from Gaussian distribution claims. Further AI assistance authored the 33 proposed two-observation Schur regression and positive-definite covariance proof scripts, source-to-report mappings and checks. They do not establish stochastic Gaussian conditioning or observed IQ population behavior. All edits to the inventory and proof register were AI-assisted. Final source-proof claims must be checked by the pinned Rocq 9.2 CI workflow, not inferred from this document's prose.

### Continuation D026x — two-observation regression sensitivity (November 15, 2026)

The extension to `TwoObservationSchur.v` contributes **31 report-relevant real-algebra theorems** about the symmetry of reordering observations, variance-energy polarization and parallelogram identities, strict convexity and unique equality cases for least-squares risk, simultaneous comparison with both one-test predictors, and the necessary-and-sufficient target-signal criterion for improvement over unconditional prediction. It additionally proves invariance of optimal Schur residual variance and affine predictions under separate nonzero measurement-unit changes of the two observed tests. These are exact scalar covariance-block results with explicit determinant and positivity assumptions. They strengthen the algebraic evidence for `thm:regression` and the standardized-score formulas; they **do not** prove Gaussian conditioning, any normal tail, or empirical IQ calibration. Verification status is determined by pinned Rocq 9.2 CI, not by this register.


### Continuation D027x — finite admissions-event dependence and conditional selection

This continuation extends `Admissions.v` by **33 new named theorems and 5 transparent definitions** mapping the Towers report's union, conditional-admission, overlap and indicator-phi discussion to exact Bernoulli four-cell algebra. Besides complementary mass and law-of-total-probability decompositions, the main substantive contributions are the **common covariance numerator of conditional pass-rate uplift, failure-stratum downlift, and cross-stratum contrasts**; exact independence and positive-association criteria for both test orientations; and the sharp four Fréchet inequalities bounding possible binary indicator covariance. Rather than defining a second event algebra or a new Gaussian model, every proof reuses `Admissions.binary_indicator_covariance_numerator`, its existing conditional numerators, and Stdlib real arithmetic. **These do not prove bivariate Gaussian integrals, infer continuous-score Pearson correlation from phi, or verify population IQ rates.** All formal status claims require passing Rocq 9.2 CI.


### Continuation D028x — sharp Fréchet realization, odds ratios and rigorous binary phi

The new `Admissions.v` extension adds **36 mathematically distinct named Rocq theorem scripts and four transparent real definitions** relevant to the Towers multiple-test admissions report. Unlike inequalities alone, the constructive Fréchet realization theorem gives an explicit normalized four-cell model for **every feasible pair of marginal acceptance rates and overlap**, with necessity/sufficiency and extremal-disjoint, nested and full-coverage witnesses. A second group relates the actual union admissions rate to the matched-marginal independence reference and proves precise conditional/odds-ratio characterizations of binary independence and positive or negative association. Finally, an exact quartic covariance-square gap factorization into four nonnegative triple-cell products gives **a direct finite Cauchy–Schwarz proof** for the binary indicator covariance, from which the normalized phi interval `[-1,1]` and its zero/sign criteria follow under strictly positive Bernoulli variances. Existing four-cell and Stdlib real operations are reused; no Gaussian-copula integration, continuous-score Pearson rho inference or empirical IQ calibration is asserted. These results are kernel-checked **only if** the pinned Rocq 9.2 workflow succeeds for the specific commit.


### Continuation D029x — two-test innovation regression and independent measurement-noise sensitivity

The D029x extension of `TwoObservationSchur.v` contains **60 proposed new named Rocq theorems and 3 transparent residualization definitions**. It derives partial covariance/innovation variance directly from the existing two-by-two Schur determinant and normal equations; proves strict improvement criteria, scale and projection invariance, exact gain polarization, covariance quadratic diagonalization, and the uncorrelated-observation simplification. It also proves noise-regularized covariance determinant formulas, fixed-predictor risk penalties, and, critically, **optimal Schur residual risk cannot improve when either or both observations acquire additional nonnegative independent diagonal noise**. This supplies source-to-report mathematical justification for sequential conditional-means information monotonicity and robust composite-score estimation, with explicit positive-minor assumptions and a sharp old-coefficient upper bound. These are exact **best-linear-predictor covariance identities**, not Gaussian conditional-law integrals, normal-tail accuracy claims or empirical psychometric validation. Proposals become kernel-checked only after passing pinned Rocq 9.2 CI.


### Continuation D030x — sharp strictness, attenuation and equality cases for independent-score noise

This continuation adds **53 substantive Rocq theorem statements** directly relevant to the sequential conditional-means and composite-IQ reports. New results characterize *exactly when* adding either score's measurement variance strictly increases the optimal best-linear-prediction residual, when the optimum is unchanged, and when the same information loss is reflected in incremental explained variance. The formal extension includes noise-order comparisons, strict monotonicity, exact partial-covariance signal criteria, preservation of regression-coefficient signs, a closed-form attenuation factor, and sharp upper/lower bounds under independent noise added to one or both scores. Proofs reuse existing Schur variance and innovation definitions and Stdlib real arithmetic rather than inventing another Gaussian model, field theory, or least-squares optimizer. **These statements are proposed until passing pinned Rocq 9.2 CI on the final commit**; they are not Gaussian conditional-law or empirical test-quality claims.


### Continuation D031x (phase 1) — weighted covariance Cauchy–Schwarz and linear regression foundations

Proposed **29 substantive source-proved finite covariance theorems**, including a general real quadratic positivity/discriminant lemma, finite weighted Cauchy–Schwarz, zero-variance support characterization, affine covariance calibration, and variance-of-sums identities. Three transparent finite-regression definitions connect these proofs to exact least-squares predictions used by the sequential conditional-means and composite-IQ reports. This phase remains provisional until pinned Rocq 9.2 kernel checks and final integration CI succeed. No Gaussian-model existence, continuous tails or empirical IQ calibration is asserted.


### Continuation D031x (phase 2) — finite one-feature least-squares and Schur explained variance

An additional **24 new Rocq theorem scripts** extend D031x to **53 proposed report-linked theorems**. The exact covariance normal equation, unique optimal linear slope, error-as-completed-square, positive and zero explained-variance criteria, and nonnegative/bounded Schur residual are tied to finite score prediction in the sequential conditional-means and composite-IQ reports. The proof layer reuses the finite weighted Cauchy–Schwarz and previously established covariance bilinearity rather than reproducing a list-recursive optimizer. All claims require pinned Rocq 9.2 verification and do not prove Gaussian distributional assumptions or empirical IQ measurements.


### D032x — finite least-squares equality and sharp supported-affinity conditions

**19 proposed additional Rocq theorems** characterize exact finite linear predictability, the equivalence between zero Schur residual, singular two-score covariance determinant, and supportwise affine target/feature equality, along with strict positivity for a non-affine supported observation. The work also derives directional regression-coefficient sign reciprocity and covariance normalization bounds. All formal claims require the pinned Rocq 9.2 kernel and documentation CI before being called proved. These statements apply to a finite nonnegative weighted enumeration and do not establish a Gaussian conditional distribution or any empirical IQ population model.


### D032x phase 2 — sharp fitted/residual covariance bounds and equality on supported outcomes

This phase proposes **26 further Rocq theorems**, bringing D032x to **45 named theorem scripts**. It formalizes Cauchy–Schwarz and positive-semidefinite Gram bounds for conditional fitted/residual scores, the between-cell and within-cell covariance matrices, exact supportwise conditions for zero residual variance or zero fitted variance, sharp equality characterizations of the finite total-variance decomposition, and links between conditional cross-covariance and strictly positive original-score variances. All work reuses existing finite two-cell projection, finite conditional covariance, and previously proved finite Cauchy–Schwarz rather than duplicating integration or regression routines. Claims count as formally proved only after pinned Rocq 9.2 and repository CI pass. These results do not establish Gaussian conditional laws or empirical IQ distribution parameters.

### D033x — central reusable libraries and report-specific proof ownership

The eighteen Rocq proof modules have been moved, *without copying their source bodies*, into one central report-independent [mathematical library](../library/rocq/README.md) and three specialized theorem directories: `analyses/hoeflin-ferguson/rocq/` (Hoeflin); `analyses/towers-multiple-test-admissions/rocq/` (Admissions and FourCellBridge); and `analyses/sequential-conditional-means/rocq/` (SequentialReport, the three equicorrelation spectral/vector modules, ReportRounding and ReportCounterexample). The exact module and theorem names are preserved and 1,682 scripts remain in the proof register. The new [clean compile script](../scripts/compile_rocq.sh) assembles precisely one copy of each module before the pinned Rocq 9.2 kernel check. Report-independent finite covariance theorems have one canonical owner in `library/rocq/`, while the report-dependent equicorrelation spectral/vector proofs have one canonical owner in the Sequential proof folder. Source relocation does not create additional mathematical theorems and does not establish Gaussian conditioning or empirical IQ validity.

## Appendix — Complete AI disclosure

D032x source theorems, mathematical scope analysis, comments, and report-to-proof mapping were prepared with AI assistance. Kernel compilation checks proof terms for exact propositions; source documentation or compilation does not independently validate IQ population assumptions, normality, Gaussian tail integrals, or empirical test parameters.

D031x finite covariance and least-squares proof scripts, theorem mappings, comments and refactoring choices were generated with AI assistance. Only the exact Rocq kernel-checked propositions under their stated premises count as established. The finite weighted sample algebra does not verify Gaussian conditional laws, empirical IQ distributions, or numerical tail integrals.

D030x theorem statements, proof scripts, source-to-report mapping, documentation and refactoring choices were AI assisted. CI success is necessary to count any script as Rocq-kernel proved. No bivariate normal existence theorem, Gaussian conditional probability, continuous normal-tail integral, empirical test correlation or experimental IQ-population claim follows from these finite covariance identities.

D029x proof source, new covariance residualization definitions, theorem statements, proof refactoring decisions and inventory mapping were generated with AI assistance. Only kernel-checked statements under their exact premises can count as formally verified. These finite algebraic results do not establish Gaussian conditional distributions, continuous normal tails, numerical tail certificates or real IQ test population parameters.

D028x source proof scripts, 36 new theorem statements and four definitions, and the associated report mapping were drafted with AI assistance. The underlying Rocq kernel and separately pinned test workflows—not this text—determine whether a claim is proved; finite binary-event identities cannot validate Gaussian assumptions or observed IQ rates.

The D027x admissions dependence extension, its 33 new theorem proof drafts, and its source-to-report mapping were prepared with AI assistance. Rocq kernel compilation is required before interpreting any draft theorem as verified. No continuous Gaussian model, normal tail integral or empirical psychometric property has been established.

This source-based theorem inventory, its continuation entries, and associated formal proof work were drafted and reviewed with assistance from OpenAI's ChatGPT. Mathematical results are valid only to the extent that their exact propositions are accepted by the Rocq kernel under their stated hypotheses. CI, finite arithmetic, and test checks do not verify the continuous Gaussian-model assumptions, numerical tail-integral accuracy, or any empirical test-population parameter. Repository maintainers remain responsible for independent source review and application of these model-limited claims.
