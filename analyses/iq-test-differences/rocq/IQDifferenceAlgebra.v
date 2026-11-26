(** Module: IQDifferenceAlgebra.v
    Purpose: Record exact scalar algebra used by the IQ discrepancy report.
    Mathematical representation: Real-valued covariance factors, contrasts,
    correlation averages and regression example arithmetic.
    Explicit hypotheses: Every domain restriction is stated in its theorem;
    numerical examples fix their parameters as rational real constants.
    Library use: Stdlib Reals, Lra, Ring and Field; no new axioms.
    Limitations: No Gaussian measure, integrals, conditional laws or numerical
    library correctness are established by this file.
    Reproduction: Compile using the repository's pinned Rocq workflow;
    this draft has not yet received a successful kernel check.
    Researcher/requester: Anders Hellström. *)
From Stdlib Require Import Reals Lra Psatz Ring Field List.
Require Import FiniteSum PooledMomentsAlgebra.
Import ListNotations.
Open Scope R_scope.

(** [iq_gap_variance]
    Mathematical meaning: Expand the covariance-based variance of a two-score contrast.
    Exact representation: The two marginal variances are sigma squared and the covariance is sigma squared times rho.
    Premises and side conditions: All real sigma and rho; a covariance interpretation additionally requires an admissible correlation and a finite variance.
    Proof/definition method: Ring normalization expands the two copies of the marginal variance and factors the correlation term.
    Library reuse: Stdlib real arithmetic and ring; no custom algebra engine.
    Boundary: Only a scalar identity, not a theorem about random variables. *)
Theorem iq_gap_variance (sigma rho : R) :
  sigma * sigma + sigma * sigma - 2 * (sigma * sigma * rho)
  = 2 * sigma^2 * (1-rho).
Proof. ring. Qed.

(** [iq_gap_variance_nonnegative]
    Mathematical meaning: The Gaussian contrast variance factor is nonnegative.
    Exact representation: The nonnegative factors are twice sigma squared and one minus rho.
    Premises and side conditions: The upper bound rho <= 1 is sufficient for this claim; it does not enforce the full correlation domain.
    Proof/definition method: Apply nonnegativity of multiplication and linear/nonlinear real arithmetic to the factors.
    Library reuse: Stdlib real order lemmas and nra/lra.
    Boundary: Does not establish existence of a covariance model. *)
Theorem iq_gap_variance_nonnegative (sigma rho : R) :
  rho <= 1 -> 0 <= 2 * sigma^2 * (1-rho).
Proof. intros H. apply Rmult_le_pos; [nra | lra]. Qed.

(** [iq_block_average]
    Mathematical meaning: The duplicated three-plus-two model has average correlation three fifths.
    Exact representation: Four within-group pairs contribute one each and six cross-group pairs contribute one third.
    Premises and side conditions: The counts and pair correlations are fixed numerical premises, not an estimated sample correlation.
    Proof/definition method: Field normalization computes the rational mean of the ten pairs.
    Library reuse: Stdlib field tactic for real rational arithmetic.
    Boundary: Does not formalize Gaussian dependence or the probability law. *)
Theorem iq_block_average : (4 + 6 * (1/3)) / 10 = 3/5.
Proof. field. Qed.

(** [iq_smooth_mixture_average]
    Mathematical meaning: Equal mixture weights give a mean correlation of three fifths.
    Exact representation: The component correlations are three tenths and nine tenths.
    Premises and side conditions: Equal mixture weights and fixed marginal moments are needed for the statistical interpretation.
    Proof/definition method: Normalize the rational arithmetic in the average.
    Library reuse: Stdlib field arithmetic.
    Boundary: Total covariance and existence of the mixture are separate results. *)
Theorem iq_smooth_mixture_average : (3/10 + 9/10)/2 = 3/5.
Proof. field. Qed.

(** [iq_conditional_example]
    Mathematical meaning: The regression contrast at first score 145 equals 18.
    Exact representation: The multiplier is one minus the correlation three fifths, applied to the 45-point displacement.
    Premises and side conditions: The input parameters are fixed; Gaussian regression is not a premise proved here.
    Proof/definition method: Normalize the displayed rational expression.
    Library reuse: Stdlib field arithmetic.
    Boundary: The conditional mean law itself is outside this lemma. *)
Theorem iq_conditional_example : (1-3/5)*(145-100)=18.
Proof. field. Qed.

(** [iq_conditional_variance_example]
    Mathematical meaning: The residual variance in the numerical regression example is 144.
    Exact representation: The marginal variance is 225 and the residual factor is one minus squared correlation.
    Premises and side conditions: The chosen standard deviation and correlation are exact rational constants.
    Proof/definition method: Use field normalization on the squared terms.
    Library reuse: Stdlib field arithmetic and real powers.
    Boundary: No conditional density or Gaussian independence claim is made. *)
Theorem iq_conditional_variance_example : 15^2*(1-(3/5)^2)=12^2.
Proof. field. Qed.

(** [iq_common_shift]
    Mathematical meaning: Adding the same shift to two scores leaves their signed difference unchanged.
    Exact representation: The common additive term is a real number that appears once in each score.
    Premises and side conditions: No positivity or distributional assumptions are needed.
    Proof/definition method: Normalize the subtraction of the two translated real expressions.
    Library reuse: Stdlib ring normalization.
    Boundary: Extending to the maximum-minus-minimum of a finite battery requires additional order arguments. *)
Theorem iq_common_shift (a x y : R) : (a+x)-(a+y)=x-y.
Proof. ring. Qed.

(** [iq_scaled_gap]
    Mathematical meaning: A common scale factors out of a signed contrast.
    Exact representation: The same real multiplier is applied to each score.
    Premises and side conditions: No sign restriction is needed for this signed identity.
    Proof/definition method: Use the distributive law via ring normalization.
    Library reuse: Stdlib ring tactic.
    Boundary: Absolute differences require an additional absolute-value identity. *)
Theorem iq_scaled_gap (s x y : R) : s*x-s*y=s*(x-y).
Proof. ring. Qed.

(** [iq_equicorrelation_domain]
    Mathematical meaning: The two equicorrelation eigenvalue factors are nonnegative.
    Exact representation: The factors correspond to the mean direction and its orthogonal complement.
    Premises and side conditions: The real dimension parameter is at least two and the scaled correlation and upper bound are explicit hypotheses.
    Proof/definition method: Split the conjunction and use linear real arithmetic on the assumed products.
    Library reuse: Stdlib lra.
    Boundary: This is the eigenvalue inequality only, not the spectral decomposition itself. *)
Theorem iq_equicorrelation_domain (k rho : R) :
  2 <= k -> -1 <= (k-1)*rho -> rho <= 1 ->
  0 <= 1+(k-1)*rho /\ 0 <= 1-rho.
Proof. intros Hk Hlow Hhigh. split; lra. Qed.

(** [iq_shared_mixture_average]
    Mathematical meaning: The shared/independent mixture has weighted correlation three fifths.
    Exact representation: The common-score component has correlation one and the independent component zero.
    Premises and side conditions: The mixture weights are three fifths and two fifths.
    Proof/definition method: Use field normalization of the weighted sum.
    Library reuse: Stdlib field arithmetic.
    Boundary: Total covariance and marginal distribution invariance remain separate probability arguments. *)
Theorem iq_shared_mixture_average : (3/5)*1+(2/5)*0=3/5.
Proof. field. Qed.

(** [iq_absolute_shift]
    Mathematical meaning: A common translation preserves the absolute gap.
    Exact representation: Absolute differences of two real scores after an arbitrary shift.
    Premises and side conditions: No probability, sign or scale restrictions are needed.
    Proof/definition method: Rewrite with the already proved common-shift identity.
    Library reuse: iq_common_shift and Stdlib Rabs.
    Boundary: Pointwise, not a statement about random-variable integrals. *)
Theorem iq_absolute_shift (a x y : R) :
  Rabs ((a+x)-(a+y)) = Rabs (x-y).
Proof. now rewrite iq_common_shift. Qed.

(** [iq_absolute_scale]
    Mathematical meaning: A common nonnegative scaling multiplies the absolute gap.
    Exact representation: The absolute value of a scaled difference factors as scale times gap.
    Premises and side conditions: Require a nonnegative real scale; scores are arbitrary reals.
    Proof/definition method: Rewrite the signed scale identity, multiplicativity of absolute value, and absolute value of a nonnegative number.
    Library reuse: iq_scaled_gap, Rabs_mult and Rabs_right from Stdlib.
    Boundary: No stochastic assumptions or Gaussian moment formulas. *)
Theorem iq_absolute_scale (s x y : R) :
  0 <= s -> Rabs (s*x-s*y) = s*Rabs (x-y).
Proof.
  intro Hs. rewrite iq_scaled_gap, Rabs_mult, (Rabs_right s); [reflexivity|lra].
Qed.

(** [iq_range_pair_square_bound]
    Mathematical meaning: Every squared pairwise gap is bounded by the sum of all squared pairwise gaps.
    Exact representation: A finite list of real signed gaps contains the particular signed gap being bounded.
    Premises and side conditions: Require list membership; no positivity assumptions on signed gaps.
    Proof/definition method: Apply the canonical nonnegative member bound to the square integrand and establish square nonnegativity by real arithmetic.
    Library reuse: FiniteSum.finite_sum_member_le, Stdlib List and nra.
    Boundary: This proves the finite pointwise inequality underlying the range bound; expectation and the enumeration of extrema are separate. *)
Theorem iq_range_pair_square_bound (ds : list R) (d : R) :
  In d ds -> d*d <= finite_sum (fun x => x*x) ds.
Proof.
  intro Hd.
  (* Supply the square integrand explicitly; higher-order unification of
     d*d otherwise chooses the unintended function fun x => d*x. *)
  apply (@finite_sum_member_le R ds (fun x : R => x*x) d).
  - intros x Hx. nra.
  - exact Hd.
Qed.

(** [iq_gap_heterogeneous_variance_nonnegative]
    Mathematical meaning: The heterogeneous contrast variance is nonnegative on the upper correlation domain.
    Exact representation: The variance decomposes into a squared scale difference plus a nonnegative covariance adjustment.
    Premises and side conditions: Require nonnegative scales and rho <= 1.
    Proof/definition method: Use the exact square decomposition and nonnegativity of the remaining product.
    Library reuse: Stdlib ring, nra, Rmult_le_pos.
    Boundary: The law of the contrast and its folded-normal expectation are not implied by this algebra alone. *)
Theorem iq_gap_heterogeneous_variance_nonnegative (sx sy rho : R) :
  0 <= sx -> 0 <= sy -> rho <= 1 ->
  0 <= sx^2+sy^2-2*rho*sx*sy.
Proof.
  intros Hx Hy Hr.
  assert (Hp : 0 <= 2*sx*sy*(1-rho)).
  { apply Rmult_le_pos; [apply Rmult_le_pos; [lra|exact Hy]|lra]. }
  assert (Hs : 0 <= (sx-sy)^2) by nra.
  nra.
Qed.

(** [iq_two_component_scale_concavity]
    Mathematical meaning: The equal-weight mean of two square-root scales is no larger than their root mean square.
    Exact representation: Two nonnegative scales a and b model the conditional residual scales of an equal-weight mixture.
    Premises and side conditions: Require a,b nonnegative; the inequality is stated on squared scales to avoid a redundant root monotonicity proof.
    Proof/definition method: Expand the deficit as a nonnegative squared difference.
    Library reuse: Stdlib nra and real squares.
    Boundary: An algebraic two-component Jensen instance, not a general probability Jensen theorem. *)
Theorem iq_two_component_scale_concavity (a b : R) :
  ((a+b)/2)^2 <= (a^2+b^2)/2.
Proof. assert (H : 0 <= (a-b)^2) by nra; nra. Qed.

(** [iq_parallel_variance_identity]
    Mathematical meaning: Combining two centered blocks retains the between-block sum of squares.
    Exact representation: Positive real block sizes and block means; pooled mean is defined by its weighted sum.
    Premises and side conditions: Require both sizes positive, so their sum is nonzero.
    Proof/definition method: Instantiate the canonical centered pooling identity, then translate its notation using field and ring normalization.
    Library reuse: PooledMomentsAlgebra.pooled_between_centered_identity; Stdlib field and ring.
    Boundary: Exact real arithmetic, not a floating-point rounding certificate. *)
Theorem iq_parallel_variance_identity (na nb a b : R) :
  0 < na -> 0 < nb ->
  let m := (na*a+nb*b)/(na+nb) in
  na*(a-m)^2+nb*(b-m)^2 = na*nb/(na+nb)*(b-a)^2.
Proof.
  intros Ha Hb. cbv zeta.
  replace ((na*a+nb*b)/(na+nb)) with (pooled_mean na nb a b) by reflexivity.
  replace (na*nb/(na+nb)*(b-a)^2) with (pooled_between na nb a b)
    by (unfold pooled_between, pooled_mass; field; lra).
  rewrite <- (pooled_between_centered_identity na nb a b Ha Hb).
  ring.
Qed.
