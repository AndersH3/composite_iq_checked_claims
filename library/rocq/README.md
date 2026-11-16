# Shared Rocq mathematical source

**Current full-corpus checkpoint:** The pinned Rocq 9.2 kernel accepted 3,378 proof scripts in 39 modules at D049x source revision `87227eef93b3`. The 120 additional proofs are report-local and reuse this shared library. The earlier D048x 3,258-script numbers below are historical checkpoints, not the latest corpus count. AI assisted proof development; only kernel acceptance establishes the exact propositions.

## D048x — finite-sample contrast Cauchy–Schwarz and covariance feasibility

**AI disclosure:** OpenAI ChatGPT assisted theorem specifications, proofs, refactoring and this audit; only successful Rocq 9.2 kernel checks at an exact source SHA establish the formal statements.

The new shared [`SampleContrastCauchy.v`](SampleContrastCauchy.v) adds **142 Rocq-9.2-checked proof scripts**: two canonical finite centered-cross/Cauchy–Schwarz bridges, 136 explicit inequalities for pairs of sixteen four-test score contrasts, and four general consequences covering zero variance, uncorrelatedness and the sharp two-sided AM–GM covariance bounds. The [source-ordered register](../../rocq/PROOF_REFACTOR_SAMPLE_CAUCHY.md) distinguishes the one reusable inequality from its related contrast specializations.

All statements apply to **finite weighted samples** with nonnegative occurrence weights and positive total mass where required. They support `pf:moments` / G01 and composite-covariance feasibility in the Hoeflin/Ferguson, Towers and Sequential volumes, but do not prove the general random-variable version of Cauchy–Schwarz, Gaussian conditioning, normal tails, independent binomial laws, chi-square sampling pivots, confidence coverage or empirical IQ assumptions. No standalone probability model or duplicate finite-sum recursion was added.

**Author:** Anders Hellström.

> **AI disclosure:** This source-location refactor and accompanying documentation were AI-assisted; only the separately pinned Rocq kernel checks theorems.

## D047x — four-test covariance contractions and finite-list bridges (169 proof scripts)

**Author:** Anders Hellström. **AI disclosure:** OpenAI ChatGPT assisted statement design, polynomial expansion, proof scripting and this register. Kernel compilation at an exact source revision—not text or code generation—determines proof status.

The new shared [`FourContrastCovariance.v`](FourContrastCovariance.v) has **169 explicit theorem proofs and 3 definitions**. Fourteen general matrix-bilinearity/quadratic identities and 136 exact variance/covariance evaluations of 16 meaningful score contrasts establish the symbolic contraction algebra. The remaining 19 proofs establish actual finite-list covariance linearity, four-test sample covariance and variance matrix bridges, nonnegative empirical covariance quadratic forms under nonnegative sample weights and positive mass, six applied composite-score formulas, and four-score sample mean linearity.

For the shared report proposition `pf:moments` (G01) this provides a direct **deterministic four-score finite-sample analogue** of `Var(w^T X)=w^T Sigma w` and `E(w^T X)=w^T mu`, plus the constructive positive-semidefinite sample covariance result. The D046x pooling results underpin the moment calculations (G12). The 136 evaluations are *related specializations* of one symmetric polynomial, not 136 independent scientific discoveries.

**Checked inventory when validated at the final source head:** 3,116 proof scripts, 3,102 public theorem/lemma/example statements, 3,414 documented declarations, across 37 modules. The symbolic ten-entry covariance form does **not** assert feasibility for arbitrary real matrix inputs: PSD is proved only for matrices constructed from nonnegative-weight finite samples. The report's general random-variable expectation theory, Gaussian conditional distributions, normal tails, chi-square pivots, independent binomial laws, interval coverage, Monte Carlo accuracy, and empirical IQ-model assumptions remain outside these finite/algebraic statements.

## D046x — general finite-list weighted moments and rate diagnostics

The new [`ListPoolingAlgebra.v`](ListPoolingAlgebra.v) extends the
two- and three-batch report formulas to an **arbitrary finite list** via
the canonical `FiniteSum` fold, with no duplicate recursion or custom
probability engine. It proves **159** documented theorems and introduces
**16** definitions for weighted moment aggregation, centered sums,
cross-covariance and ideal heterogeneous Bernoulli diagnostics.
The [Rocq 9.2 proof workflow](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43847174190) passed at exact commit `469f2cb2ed`.
The authoritative per-proof review is
[`PROOF_REFACTOR_LIST_POOLING.md`](../../rocq/PROOF_REFACTOR_LIST_POOLING.md).
The canonical build totals **36 modules and 2,947 proof scripts**.
Only deterministic finite-list and hypothetical parameter algebra is
certified; independent sampling distributions, Gaussian/chi-square
results, exact confidence coverage and IQ model validity remain open.

**AI disclosure:** OpenAI ChatGPT assisted theorem specification, Rocq proof scripts, algebraic library reuse, documentation, CI diagnosis and source refactoring. Only explicitly stated Rocq propositions checked by the pinned kernel are mathematical proofs. No stochastic model, confidence coverage, empirical IQ validity or independent human validation is inferred.

## D045x — new shared three-cohort diagnostic module

The canonical [`StratifiedBernoulli.v`](StratifiedBernoulli.v)
adds **185 kernel-checked theorems** on three heterogeneous Bernoulli
event-rate moment *targets*, exposure-weighted success/failure counts,
sharp variance bounds, squared benchmark calibration error and pairwise
rate dispersion. The most useful decomposition is a weighted
three-cohort ANOVA certificate, reused by additional rate-error proofs.
The [pinned Rocq 9.2 run](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43832111166) succeeded on `028d427d74a6fd8d81d9060d1feaa68aecbf96db`.
All individual declarations have detailed comments and occur in the
source-ordered proof register. The module imports `SamplingPrecision`
and `TwoRatePrecision`; there is no new sampling engine, axioms,
independent-trial probability-law proof or empirical IQ validation.
The total canonical build now contains **35 modules** and **2,788**
explicit proof scripts. AI-assisted source work is subject to Rocq
kernel validation.

## D044x — three-batch and heterogeneous-rate formalization

The canonical [`ThreeGroupPooling.v`](ThreeGroupPooling.v) module proves
**39** theorems for 3 pooled replicate groups, including the exact
associativity of corrected sum-of-squares pooling with the existing
two-group `PooledMomentsAlgebra.v` definitions. The canonical
[`TwoRatePrecision.v`](TwoRatePrecision.v) proves **72** complementary
rate-contrast, expected-count and Bernoulli count-variance results,
reusing `SamplingPrecision.v` rather than constructing a second
statistical library. The [Rocq 9.2 kernel validation](https://github.com/AndersH3/composite_iq_checked_claims/actions/runs/43819739947)
accepted all 111 new proof blocks. The 34-module source order and
source-by-source review are checked by the canonical build/documentation
scripts. Arbitrary-list pooling, independent-sampling laws and
interval-coverage results remain separate. This mathematical documentation and proof development were AI-assisted; mathematical validity applies only to explicit Rocq propositions accepted by the pinned kernel. Neither empirical IQ assumptions nor stochastic sampling distributions are proved by these real-algebra results.

## D043x — shared statistical-algebra modules

The four newly checked shared Rocq modules are
[`WilsonScoreAlgebra.v`](WilsonScoreAlgebra.v) (36 exact score algebra theorems),
[`SamplingPrecision.v`](SamplingPrecision.v) (45 conditional Bernoulli
moment/precision theorems),
[`ConditionalRatioStability.v`](ConditionalRatioStability.v) (30 exact
positive-denominator ratio theorems) and
[`PooledMomentsAlgebra.v`](PooledMomentsAlgebra.v) (31 two-batch pooled
variance identities). They reuse Stdlib real algebra, Field, Psatz and Ring;
there is no new recursive summation, binomial sampling engine or Gaussian
distribution axiom. Kernel evidence is linked from the
[formalization README](../../rocq/README.md). General probability-law and
confidence-coverage theorems remain separate obligations.

The new `TrivariateSchur.v` is the canonical generic 3×3 covariance
Schur-factorization and inequality source (27 statements, with strictly positive
conditioning variance explicit in sign-equivalence theorems). The three-test
AB|C, AC|B, and BC|A applications reside in the Towers project and simply
instantiate the shared results. Gaussian probability laws remain unproved.

Only genuinely report-neutral mathematical modules are owned **once** under this directory: `FiniteSum`, `FiniteUnion`, `FiniteMoments`, `FiniteBridge`, finite two-cell and nested projection, finite conditional covariance/residual, `TwoObservationSchur`, and `TwoStratumAssociation` (44 exact report-neutral Simpson-effect identities and inequalities), and `TwoStratumReversal` (50 necessary-and-sufficient pooled association, conditional-rate and selection-ignorability threshold criteria). They reuse Rocq's maintained Stdlib List, Reals, Lra, Psatz, and ring/field tactics. No new axioms, alternative summation recursion or Gaussian oracle are introduced.

Report-specific lemmas and models remain with their reports: [Hoeflin/Ferguson](../../analyses/hoeflin-ferguson/rocq/), [Towers admissions](../../analyses/towers-multiple-test-admissions/rocq/), and [Sequential conditional means](../../analyses/sequential-conditional-means/rocq/).

The canonical 35-module dependency order is encoded in [`scripts/compile_rocq.sh`](../../scripts/compile_rocq.sh). It copies each uniquely named source into a clean temporary workspace and runs `rocq compile` in that order. From the repository root:

```sh
bash scripts/check_rocq_documentation.sh
sh scripts/compile_rocq.sh
```

CI pins `rocq/rocq-prover:9.2.0`; an explanatory header and full declaration-specific documentation are enforced. The existing 1,682 proof scripts were relocated **without altering their propositions**; the 55 new report-specific sensitivity proofs are separately owned in SequentialSensitivity.v; 55 specialized three-test admissions proofs reside in ThreeTestAdmissions.v and import FiniteUnion/FiniteSum; ThreeTestPairBridge.v contributes 84 cross-model pairwise proofs and three certified two-event constructors; ThreeTestConditionalStrata.v adds 126 conditional-selection and Simpson-reversal theorems with eight model-construction proofs using the already checked Admissions library. Finite weighted algebra and best linear prediction do not themselves establish Gaussian conditional probabilities, normal-tail integrals, or any empirical psychometric parameter.

## Complete AI disclosure

OpenAI ChatGPT classified and relocated the source and updated the compile scripts. Only Rocq-kernel-checked statements under their actual hypotheses constitute formal results, and these results must not be interpreted as validation of Gaussian or real-world IQ assumptions.
