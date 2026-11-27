# All eight reports: mandatory Rocq proof obligations

**AI DISCLOSURE — AI-assisted source audit and proof planning.** Researcher/requester: **Anders Hellström**. The inventory is not a proof certificate. No newly listed result is counted as kernel-proved merely because an algebraic analogue or a written proof exists.

Audit baseline: `e790af0559c716596d2d251af32057879689672c` (November 27, 2026). All 58 tracked TeX sources at this baseline have been retrieved and indexed, including the eight root reports, included proof chapters, shared foundations, claim maps, numerical inputs, and presentation templates. The seven separate indices were checked against the complete tracked TeX file list: no missing or duplicate paths. This register supersedes the [historical six-report scope](SIX_REPORT_PROOF_OBLIGATIONS.md); retain G01–G24 and the existing detailed proof mappings. G25–G30 extend them for IQ differences.

## Mandatory acceptance policy

1. Every deductive mathematical assertion in every report (including inline prose, unlabelled equations, abstracts, highlights, appendices, numerical tables and uncertainty formulas) must be linked to an equivalent Rocq theorem or a recorded exact instantiation of a maintained library theorem. Split compound claims. Match all hypotheses, conclusion, quantifiers, domains and degenerate cases.
2. The claim record must identify report file and source location, exact mathematical statement, proof owner and identifier, dependencies, exact source commit, successful pinned kernel build and transitive `Print Assumptions` evidence. Reuse Stdlib, MathComp, Coquelicot and FormalML rather than duplicating results. Use Rocq only. No new project axioms, Admitted, or weakened replacement statements.
3. A finite or algebraic counterpart does not discharge a general probability or distributional assertion. Mathematical derivations in XeLaTeX, successful simulations, Deal contracts, and numerical matches are not Rocq proofs. A theorem for an independent residual does not prove independence from Gaussian covariance.
4. Mathematical numerical targets need exact certificates or rigorously bounded approximations with an explicit rounding/tolerance rule. For the simulation reports, prove the mathematical reduction, uncertainty and acceptance criteria and establish the implementation-to-specification correspondence; actual execution, raw samples, historical observations and source provenance require evidence rather than purported universal proofs. State modeling assumptions explicitly; no theorem may fabricate empirical Gaussianity or PRNG independence.
5. Final acceptance requires zero unmatched deductive mathematical claims, not a theorem-count threshold. If a report claim is false or overbroad, record and correct it transparently rather than silently weakening its formal counterpart. Rebuild and inspect all eight PDFs when the mathematical and proof registers are reconciled.

## Report entry points

| Volume | Source | Detailed index |
|---|---|---|
| HF-M | [composite_iq_analysis.tex](../analyses/hoeflin-ferguson/composite_iq_analysis.tex) | [HOEFLIN](report-audit/HOEFLIN.md) |
| HF-S | [hoeflin_simulations.tex](../analyses/hoeflin-ferguson/hoeflin_simulations.tex) | [HOEFLIN](report-audit/HOEFLIN.md) |
| TW-M | [towers_admissions_analysis.tex](../analyses/towers-multiple-test-admissions/towers_admissions_analysis.tex) | [TOWERS](report-audit/TOWERS.md) |
| TW-S | [towers_simulations.tex](../analyses/towers-multiple-test-admissions/towers_simulations.tex) | [TOWERS](report-audit/TOWERS.md) |
| SQ-M | [sequential_conditional_means.tex](../analyses/sequential-conditional-means/sequential_conditional_means.tex) | [SEQUENTIAL](report-audit/SEQUENTIAL.md) |
| SQ-S | [sequential_simulations.tex](../analyses/sequential-conditional-means/sequential_simulations.tex) | [SEQUENTIAL](report-audit/SEQUENTIAL.md) |
| IQ-M | [iq_test_differences.tex](../analyses/iq-test-differences/iq_test_differences.tex) | [IQ-DIFFERENCES](report-audit/IQ-DIFFERENCES.md) |
| IQ-S | [iq_difference_simulations.tex](../analyses/iq-test-differences/iq_difference_simulations.tex) | [IQ-DIFFERENCES](report-audit/IQ-DIFFERENCES.md) |

## Source inventory

| Source group | TeX files | Formal environments | Display anchors | Labels | Source spans |
|---|---:|---:|---:|---:|---:|
| [HOEFLIN](report-audit/HOEFLIN.md) | 11 | 9 | 42 | 44 | 127 |
| [TOWERS](report-audit/TOWERS.md) | 5 | 11 | 43 | 56 | 135 |
| [SEQUENTIAL](report-audit/SEQUENTIAL.md) | 9 | 39 | 156 | 144 | 227 |
| [IQ-DIFFERENCES](report-audit/IQ-DIFFERENCES.md) | 6 | 15 | 12 | 15 | 34 |
| [SHARED](report-audit/SHARED.md) | 8 | 16 | 13 | 20 | 40 |
| [TOWERS-DATA](report-audit/TOWERS-DATA.md) | 11 | 0 | 0 | 0 | 12 |
| [SEQUENTIAL-DATA](report-audit/SEQUENTIAL-DATA.md) | 8 | 0 | 0 | 0 | 8 |
| **Total** | 58 | 90 | 266 | 279 | 583 |

The formal-environment count covers theorem/lemma/proposition/corollary blocks; shared sources are counted once. Display anchors include recognized display environments and bracket/dollar display forms. Labels include nonmathematical labels. Source spans conservatively include nonblank non-comment lines grouped by paragraphs/section boundaries, including inline math and evidence. These anchors overlap, so do not add the counts as if they were independent propositions. All 90 explicit environments have source locations, and IQ's fifteen propositions have specific new work-package mappings. Older mappings are historical leads. **Semantic splitting, individual claim classification, exact theorem equivalence, and proof closure are still open**, particularly for inline prose, compound statements and individual numeric table cells. The index is a discovery register, not a machine-enforced completeness check.

## Current verification evidence and boundaries

Computer10 at `2a77faadfc50e85113022af286cfb02e95b08f54` compiled all 45 canonical modules and 3,706 registered proof scripts using Rocq 9.3.0, including seven G26 finite-range proofs. Six MathComp Gaussian scalar probability/density theorems were compiled and independently kernel-checked. FormalML ConditionalExpectation.v and ProductSpace.v compiled incrementally with D195 under isolated Rocq 9.2.0. Both project FormalML CE modules now compile: the residual module at `2a77faa` and product module at `26342d86d97fc8a35e1b930a1c0d1c0790c66251`. All six residual and three product targets completed Print Assumptions on computer10; the union is 12 inherited logical axioms, with no project-specific axiom reported. See CONTINUATION_20261126.md for exact per-theorem matrices. The product independence is derived from the constructed product space, not arbitrary joint Gaussianity; finite moments and centering remain explicit. General Gaussian residual independence, exact regular conditional kernels, clean pinned reproduction and canonical assumption audits remain open; all ten MathComp targets now have independent kernel and transitive assumption evidence. Both FormalML compiled objects and their imported closure passed independent rocq check at `bc76b21`. The combined audit was killed, but all nine prior individual audits succeeded; separate tracked audit modules replace it. ProductLawIndependence.v (source `f8319ea`, tested at `e17d8c6`) passed compilation, transitive assumption audit (10 previously identified inherited axioms) and independent kernel check. JointLawConditionalExpectation.v (corrected source `8905a21`, tested at `a7f2139`) passed compilation, independent kernel check and all three transitive audits (10, 10, 12 inherited axioms). The joint-law factorization, integrability and centering hypotheses remain explicit. GaussianResidualMeasure.v (source correction `a9fd11e`, tested at `be11a25`) passed all four targets (three substantive theorems and the translation-measurability lemma), independent kernel verification and transitive assumption auditing (the same three inherited boolp axioms in every target). Combined inventory: 3706 canonical scripts, 10 MathComp targets and 13 FormalML targets, totaling 3729. GaussianOriginalResidualMeasure.v (`d29db35`) adds two original-coordinate residual mass factorization candidates; R1 failed on a real/extended-real notation scope conflict, corrected in `3a41add`, pending validation. Identification with an actual joint pushforward measure, general Gaussian joint-law factorization and cross-library representation remain open. Keep these proof counts separate.

## Retained shared proof packages G01–G24

See the [original register](SIX_REPORT_PROOF_OBLIGATIONS.md) for exact historical mappings; the following identifies remaining scope, not claims that all listed sublemmas are unproved.

| Package | Full-scope obligation | Reuse / current boundary |
|---|---|---|
| G01 | General square-integrable expectation, covariance, Cauchy–Schwarz, zero variance a.s., actual weighted scores | FiniteMoments, FourContrastCovariance; compiled FormalML expectation/L2 APIs |
| G02 | Multivariate Gaussian construction, PSD realization including degenerate cases, affine closure, characteristic-function uniqueness and block independence | EquicorrelationVectors, GaussianCovarianceDomain, MathComp scalar normal laws; full multivariate bridge missing |
| G03 | General Gaussian block regression, conditional mean and covariance, residual independence | GaussianConditionalKernel, GaussianFiniteHistoryPosterior; nine compiled/audited FormalML CE targets plus one verified product-law equivalence under explicit residual hypotheses or constructed product law; general Gaussian bridge open |
| G04 | Pointwise regular conditional laws, continuous version uniqueness, exact and singular history cases | Existing covariance algebra and scalar posterior measures; regular kernel missing |
| G05 | Normal marginal but nonjoint Gaussian countermodels, covariance and different tails | ReportCounterexample, IQ mixture algebra; actual measures missing |
| G06 | General event arithmetic, CE existence/uniqueness, tower, pull-out, total variance/covariance | FiniteUnion, FiniteNestedProjection, FiniteConditionalCovariance; compiled FormalML conditional expectation; report-scope instantiations needed |
| G07 | Independent Gaussian sampling, chi-square pivot, independence of sample mean and variance, interval coverage | Shared moment algebra; full stochastic pivot not established |
| G08 | Independent Bernoulli/binomial PMF, moments, zero counts and relative precision | SamplingPrecision, StratifiedBernoulli, TwoRatePrecision; actual distribution proof needed |
| G09 | Wilson score inversion and precise coverage scope | WilsonScoreAlgebra; match endpoints and assumptions |
| G10 | Exact equal-tail Clopper–Pearson conservative coverage | Full binomial-tail inversion and coverage proof needed |
| G11 | Conditional binomial with random denominator | Admissions and finite conditioning; actual independent trial law needed |
| G12 | Arbitrary finite group/block pooling and within/between corrected SS | ListPoolingAlgebra, PooledMomentsAlgebra, ThreeGroupPooling; connect report implementation |
| G13 | Multiple diagnostics, rare-event and sample-size bounds | FiniteUnion and sampling precision; actual probability and diagnostic model |
| G14 | Normal CDF, strict monotonicity, continuity, inverse quantiles, tail calculus | MathComp normal distribution; exact enclosures not established |
| G15 | Hoeflin common-factor aggregate, posterior, residual contrasts, optimal L2 MSE | Hoeflin and Gaussian posterior algebra; joint law missing |
| G16 | Latent nonidentification, selected populations, repeated attempts | Finite association and countermodels; full probabilistic constructions needed |
| G17 | Cross-size couplings, nested indicators and exponential bounds | Finite event and variance algebra; actual stochastic coupling needed |
| G18 | End-to-end rational arithmetic, sqrt and decimal rounding | ReportRounding, Hoeflin, SequentialReport; match each numerical target |
| G19 | Bivariate normal density, conditional joint-tail integral and Plackett derivative | ThreeTestSchur, normal measure theory; continuous tail differentiation missing |
| G20 | Towers strict bounds, unique OR calibration and nonnested Gaussian events | Admissions, finite event bounds; Gaussian continuity and analytic inequalities missing |
| G21 | BASIC grid enumeration and normalization, perturbation error for ratios | ConditionalRatioStability, Admissions, FiniteSum; full grid-to-report proof needed |
| G22 | Sequential real limits, count order, growth and square-root continuity | SequentialSensitivity, GaussianBatchBalance; connect exact limit results |
| G23 | Gaussian L2 aggregate coupling | Gaussian covariance/variance identities; actual measure/L2 convergence missing |
| G24 | Certified Gaussian tails, quantile roots, calibration and displayed decimals | No blanket numerical enclosure theorem; prove each value/tolerance |

## IQ discrepancy extensions G25–G30

| Package | Required theorem family | Report claims |
|---|---|---|
| G25 | Folded-normal mean, CDF, variance, noncentral mean, gap quantile, degenerate cases, density calculus | prop:gap, conditional, heterogeneous, quantile and numerical examples |
| G26 | Arbitrary finite Gaussian range; measurable max/min; iid maximum and unique minimum; range CDF and mean; finite moment bound, strict positivity, monotonicity, scaling and mean/range independence | prop:range, bound, sensitivity, average |
| G27 | Gaussian quadrant/arcsine law, three-dimensional sign expansion, exact five-test closed form, integration by parts and boundary limits | prop:five |
| G28 | General mixture kernel, fixed normal margins, total covariance, strict Jensen, two explicit mixtures and replicated two-group Gaussian countermodel | prop:mixtures, block |
| G29 | Truncated normal signed first moment, positive tail, event conditioning and threshold selection | prop:selection |
| G30 | Joint extrema density and double integral for range second moment, finite moment domination | prop:second |

The [IQ-specific index](report-audit/IQ-DIFFERENCES.md) maps all fifteen analytical propositions to named partial evidence and these packages. The simulation companion adds unbiased sample variance, pooled centered SS, sample-mean variance, SE estimation, exact ten-case reference enclosures and the acceptance criterion. Reuse shared G01/G07/G12/G13/G18/G24 for those rather than duplicating proofs.

## Prioritized continuation

1. Independent checking of both compiled FormalML project modules passed at `bc76b21`. The split nine-target assumption audit reproduced successfully at `30fbbc1`; perform a clean pinned build. The product-law independence bridge passed all three validation stages at `e17d8c6`; the original-space regression bridge passed all three validation stages at `a7f2139`. The four MathComp Gaussian residual measure targets passed all three validation stages at `be11a25`. Validate original-coordinate rectangle mass factorization and identify the actual joint pushforward law.
2. Establish the joint multivariate Gaussian law, affine closure, residual independence, conditional law, covariance realization and singular endpoints; instantiate all relevant sequential and Hoeflin theorems. Reuse MathComp normal probability/integration.
3. Prove shared normal density/CDF calculus, folded-normal and order-statistic results (G25–G30), Gaussian tail and calibration (G14/G19/G20). Reuse the same Gaussian quadrant result across Towers and IQ five-test derivations.
4. Prove sampling distributions and coverage, exact rounding/enclosures, finite-to-general bridges, limits, countermodels and implementation correspondence. Map individual statements across all eight volumes.
5. Close all remaining source-span and numeric-table obligations with exact Rocq theorem identifiers, proofs, reproducible kernel and assumption evidence; no report is marked fully formalized before that.

## Complete AI disclosure

OpenAI ChatGPT assisted retrieval and indexing of the pinned TeX sources, mathematical obligation classification, comparison with the historical proof register, and GitHub edits at Anders Hellström's request. Current compilation evidence comes from earlier recorded builds and the supplied computer10 transcript. This audit does not establish semantic completeness of automatic source parsing, exact equivalence of every historical theorem mapping, transitive axiom closure, numerical enclosure certification, peer review or empirical validation. No new mathematical proof is counted as verified based on this audit.
