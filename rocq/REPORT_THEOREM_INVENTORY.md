> **AI disclosure — prepared with AI assistance.** This is a source-based theorem inventory and formalization-status register, not an independent validation of any Gaussian model or empirical IQ claims. The source references and proof scopes were checked against the files listed below.

# Theorems and mathematical claims actually used in the reports

**Audit date:** November 14, 2026. **Baseline:** `main` at merge commit `0946d858b6fec14a1823cf50bd6db0beeca607df` (merged PR #4). **Proof-development branch:** `rocq-report-claim-proofs-20261114`.

The inventory is organized **by the claims in the actual report sources**, not by every theorem that happens to have been proved in Rocq. Thus the audit discriminates relevant proof work from the large general-purpose covariance library. It covers three reports and the sequential report's two included proof appendices:

- [Hoeflin/Ferguson composite-score report](../analyses/hoeflin-ferguson/composite_iq_analysis.tex).
- [Towers multiple-test admissions report](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex).
- [Sequential conditional-means report](../analyses/sequential-conditional-means/sequential_conditional_means.tex), its [foundational theorems](../analyses/sequential-conditional-means/theorem_foundations.tex), and [numerical proof certificates](../analyses/sequential-conditional-means/exact_numeric_certificates.tex).

## Verification levels (do not conflate)

**K — Kernel-checked at stated mathematical scope:** a named Rocq theorem proves the displayed finite/algebraic proposition, with its explicit hypotheses. **A — Algebraic consequence formalized:** the report's rational formula is checked, but the stochastic Gaussian premise from which the report derives it is **not** proved. **P — Report proof / cited established theorem only:** the typeset report gives a mathematical proof or reference, but no corresponding general Rocq kernel theorem has been supplied. **E — Empirical or numerical/modeling claim:** its correctness requires numerical/error-certified evaluation or assumptions about a real test population. A claim labelled P or E is not converted to K merely by a successful Rocq build.

The `SequentialReport.v` module now has **seven definitions and 37 Rocq 9.2 kernel-checked real-algebra and natural-induction theorems**. Both [Rocq push CI](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43627749197) and [Rocq pull-request CI](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43627753031) passed on commit `a6d3135c`. This verifies the stated arithmetic and finite recursion, **not** the Gaussian conditional-law claims, which remain P.

## I. Sequential conditional-means report — explicitly stated results

| Report label | Theorem actually used | Rocq implementation / reuse | Verification boundary |
|---|---|---|---|
| `thm:moments` | Linear expectation, bilinear covariance, variance of a linear composite, variance-zero iff constant a.s. | `FiniteMoments.v`: `expectation_of_general_weighted_sum`, `covariance_of_general_weighted_sums`, `variance_of_general_weighted_sum`, `zero_variance_is_constant_on_positive_mass`. | **K for normalized finite nonnegative measures**; general measure-theoretic version **P** |
| `thm:conditional` | Existence/uniqueness of conditional expectation, tower property, pull-out and law of total variance | Finite conditioning analogs in `FiniteUnion.v` and `FiniteBridge.v`; **no** general `L^1` conditional-expectation formalization | **P**, general theorem not kernel-checked |
| `thm:spectral` | Spectral PSD criterion and Gaussian realization of PSD covariances | `FiniteMoments.v` provides PSD of finite covariance forms, **not** a spectral theorem or Gaussian construction | **P**, substantial general linear algebra/probability gap |
| `thm:gaussian` | Gaussian affine transformation, covariance identification, independent blocks iff zero cross covariance | No Gaussian law or Gaussian-block independence formalization | **P** |
| `thm:regression` | Gaussian block regression mean `mu_U+C B^{-1}(v-mu_V)`, Schur conditional covariance | `FiniteMoments.v` proves **finite covariance Schur identities**, not the Gaussian conditional distribution | **P**, Schur algebra is not Gaussian regression |
| `lem:continuous-version` | Equality of continuous conditional-mean versions everywhere under full-support Gaussian conditioning | No topology/continuous-version probability kernel theorem | **P** |
| `thm:induction` | Mathematical induction on natural numbers | Rocq/Stdlib's built-in `nat_ind`; no custom induction scheme needed | **K (Stdlib)** |
| `prop:domain` | Equicorrelation matrix PSD exactly when `-1/k <= c <= 1`; all finite sizes require `0 <= c <= 1` | Nonnegative-correlation denominator case in `SequentialReport.v`; general spectrum and Gaussian realization absent | **A for simple denominator positivity**, **P for full theorem** |
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
| `prop:counterexample` | Equal marginal means, variances, correlation can conceal different conditional means | The finite covariance formalization supplies foundations, but explicit finite eight-occurrence counterexample in `SequentialReport.v`, with same marginal means, variances and zero cross-moment yet unequal conditional means on positive-mass history | **K for the finite countermodel and positive-atom conditional means**; not a Gaussian regression theorem |
| `cor:exact-iq-values` | Exact fractions `100+50r(3N+2)/(N(3r+2))`, `45(3N+2)/N`, `90k(3N+2)/(N²(3r+2))` | `sequential_iq_mean_exact`, `sequential_iq_population_variance_exact`, `sequential_iq_conditional_variance_exact` | **A** for the exact fraction formulas; the probabilistic interpretation has the above prerequisites |
| `lem:rounding` | Rigorous rational interval tests for nearest-decimal mean and square-root SD, including tie exclusion | Report's integer certificates are recorded in `exact_numeric_certificates.tex`; Rocq proofs of the general rational and squared-SD nearest-decimal rounding criteria in `SequentialReport.v` | **K for the general strict rational/SD rounding criteria**; individual numeric certificates still require machine checking |

### Additional consequential labelled sequential formulas

| Report equation(s) | Mathematical role | Checked algebra / remaining gap |
|---|---|---|
| `eq:inverse`, `eq:coefficient` | Inverse of equicorrelation block and regression coefficient | Scalar denominator calculations in `SequentialReport.v`; **general matrix inverse proof not yet kernel-checked** |
| `eq:recursion`, `eq:all-predictions`, `eq:answer`, `eq:multiple-recursion`, `eq:multiple-predictions`, `eq:multiple-mean` | Recursion and inclusive means | The complete natural-number induction is **kernel-checked** in `sequential_recursive_history_sum_closed_form` and `sequential_recursive_prediction_constant`; Gaussian conditional-law justification remains open |
| `eq:population-variance`, `eq:multiple-population-sd` | General finite average variance | `FiniteMoments.v`, `Hoeflin.v`, and `SequentialReport.v` |
| `eq:conditional-variance`, `eq:multiple-conditional-variance` | Conditional covariance of Gaussian scores | Rational residual simplification checked; **probabilistic conditional-covariance theorem open** |
| `eq:iq150-mean`, `eq:iq150-population-sd`, `eq:iq150-conditional-sd` | Reporting-scale conversion | The rational mean and **squared SD** formulas are checked; sqrt as a nonnegative SD still relies on report's interpretation |
| `eq:fixed-sd` | A fixed recursion output is deterministic; its SD is zero | Constant variance is already a finite-moment identity, not the conditional SD of the random test-score mean |

## II. Hoeflin/Ferguson composite-score report

The report gives labelled equations rather than a separate list of theorem environments. These are the **theorem-level mathematical identities used**, with the essential probability/model boundaries.

| Report equation | Claim | Rocq evidence and status |
|---|---|---|
| `eq:variance-sum` | `Var(X+Y)=Var(X)+Var(Y)+2Cov(X,Y)` | **K finite:** `FiniteMoments.variance_of_two_weighted_scores`, bilinearity and symmetry |
| `eq:standardize` | `z_i=(x_i-mu_i)/sigma_i` | A definition, assuming `sigma_i>0`; not a standalone stochastic theorem |
| `eq:weighted-variance` | `Var(wᵀZ)=wᵀRw` | **K finite:** `FiniteMoments.covariance_matrix_quadratic_form_is_variance` and `variance_of_general_weighted_sum` |
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
| `eq:model`, `eq:cutoffs` | Joint bivariate Gaussian assumption and marginal normal quantiles | **P/E**; model definition/quantile input, not implied by knowing the correlation |
| `eq:joint` | Bivariate Gaussian joint exceedance integral | **P**; no continuous Gaussian integration proof in the current Rocq modules |
| `eq:union` | `P(A union B)=p_A+p_B-J` | **K:** `Admissions.v`, `FiniteUnion.two_event_union_probability` |
| `eq:conditionals` | `P(B|A)=J/p_A`, `P(A|B)=J/p_B` | **K:** `Admissions.conditional_B_numerator` and `conditional_A_numerator`; positive denominators required |
| `eq:phi` | Binary-indicator phi/covariance relation, distinct from underlying continuous Pearson `rho` | **K** for indicator covariance numerator via `Admissions.binary_indicator_covariance_numerator` and `FiniteBridge.finite_event_indicator_covariance`; normalized phi requires nonzero marginal variances |
| `eq:bounds` | Finite union probability between max marginal and min(1,sum) | **K:** `FiniteUnion.arbitrary_union_bound`, `normalized_arbitrary_union_at_most_one` |
| `eq:equal-results`, `eq:mixed-joint`, `eq:mixed-conditionals`, `eq:mixed-remainder`, `eq:union-denominator` | Published bivariate-normal numeric cases and different denominators | **K** for algebra conditional on an asserted joint mass; **E** for numeric Gaussian tail integrals and rounding |
| `eq:rarity`, `eq:calibration` | Normal rarity-equivalent conversion and inverse cutoff calibration | **E**, requires normal quantile and certified root-finding, not finite event algebra |
| `eq:grid` | Legacy finite-grid Gaussian density ratio | Generic finite sums are checked in `FiniteSum.v`; the particular quadrature truncation/error is **E** |
| `eq:rho-integral` | Bivariate normal overlap as integral of density with respect to correlation | **P**, requires differentiability/integration of Gaussian law and is not currently kernel-checked |

## IV. Proof-development priorities based on report dependence

1. **Highest impact, genuinely missing:** Gaussian regression, conditional expectation (with regular conditional laws and continuous versions), and equicorrelation positive-semidefinite/spectral construction. The current Schur covariance theorems do **not** establish these stochastic claims.
2. **Checked in the maintained finite/reals infrastructure:** complete finite-history induction, two/three-start closed-form means, residual variance and exact IQ arithmetic. `SequentialReport.v` proves **37** real-algebra and induction statements, conditioned on the stated model inputs. General Gaussian regression and conditional probability laws remain open.
3. **Numerical certification:** checked individual numeric certificate instances and bivariate-normal tail/quantile error bounds. Existing Python/SciPy regression tests are valuable but do not constitute Rocq proofs of continuous probability integrals.
4. **Finite-model counterexample:** explicitly exhibit two finite joint distributions with the same marginals and covariance but different conditional means, discharging `prop:counterexample` without introducing unsupported Gaussian claims.

The table is a scope audit: it intentionally does **not** claim that every source theorem has already been formalized. Existing checked results retain their exact finite-model hypotheses; a well-documented report proof or citation is not automatically a kernel proof.

---

## Appendix — Complete AI disclosure

This inventory was researched, extracted, organized, and drafted by OpenAI's AI assistant using the connected GitHub repository. The assistant read the three primary XeLaTeX reports, two sequential-report appendices, existing Rocq theorem modules, compilation workflow, and proof-refactor register. It generated the 37-theorem and seven-definition `SequentialReport.v` algebraic and natural-induction formalization and mapped individual report labels to named proof declarations. Where a theorem involves Gaussian laws, measure-theoretic conditional expectations, matrix spectral properties, inverse-normal calculations, or floating-point error bounds not represented in Rocq, the inventory explicitly says so. The assistant did not independently validate the empirical applicability of any IQ model or change any evidence artifacts. Final source-proof claims must be checked by the pinned Rocq 9.2 CI workflow, not inferred from this document's prose.


## November 14 follow-up: checked report rounding criteria

Five new Rocq 9.2 candidate proofs correspond directly to `lem:rounding`:
integer grid separation, the strict midpoint unique-nearest criterion,
exact rational certificate sufficiency, strict squared-interval transfer
to nonnegative standard deviation, and exact SD certificate sufficiency.
These results establish **strict uniqueness**, excluding halfway ties,
with explicit positive denominators and scales. The reported 9+18
specific integer certificates are separate inputs until independently
kernel-checked. Gaussian conditional-expectation, spectral and continuous
numerical integration claims remain outside this arithmetic layer.


## Concrete positive-probability conditional-mean counterexample

Nineteen report-directed Rocq theorems certify an eight-outcome uniform
finite probability construction. The common first score has marginal
(-sqrt(2),0,sqrt(2)) with weights (1/4,1/2,1/4). Both second-score
marginals are ±1 with probabilities 1/2 each. In both joint models the
marginal score means are zero, the second moments are one, and the cross
moment is zero. But at the identical history event X=0 of positive mass
1/2, the dependent second score has conditional mean -1, while the
balanced comparison has conditional mean 0; the fixed recursive
averages are respectively -1/2 and 0. Every expectation reuses
FiniteSum.finite_sum. This checks the finite `prop:counterexample`
without asserting any Gaussian law or any general independence theorem.
