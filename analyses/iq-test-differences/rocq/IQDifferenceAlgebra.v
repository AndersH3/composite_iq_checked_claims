(** Module: IQDifferenceAlgebra.v
    Purpose: Record exact scalar algebra used by the IQ discrepancy report.
    Mathematical representation: Real-valued covariance factors, contrasts,
    correlation averages and regression example arithmetic.
    Explicit hypotheses: Every domain restriction is stated in its theorem;
    numerical examples fix their parameters as rational real constants.
    Library use: Stdlib Reals, Lra, Ring and Field; no new axioms.
    Limitations: No Gaussian measure, integrals, conditional laws or numerical
    library correctness are established by this file.
    Reproduction: Compile using the repository's canonical Rocq workflow.
    The original 16 scripts compiled on Rocq 9.3.0 at 799af85; the
    appended mixture certificates require independent kernel revalidation.
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
    Library reuse: Stdlib ring, Rle_0_sqr, Rplus_le_le_0_compat, Rmult_le_pos.
    Boundary: The law of the contrast and its folded-normal expectation are not implied by this algebra alone. *)
Theorem iq_gap_heterogeneous_variance_nonnegative (sx sy rho : R) :
  0 <= sx -> 0 <= sy -> rho <= 1 ->
  0 <= sx^2+sy^2-2*rho*sx*sy.
Proof.
  intros Hx Hy Hr.
  assert (Hp : 0 <= 2*sx*sy*(1-rho)).
  { apply Rmult_le_pos; [apply Rmult_le_pos; [lra|exact Hy]|lra]. }
  (* The standard square lemma supplies positivity explicitly, rather
     than asking nonlinear arithmetic to discover a difference square. *)
  pose proof (Rle_0_sqr (sx-sy)) as Hs.
  unfold Rsqr in Hs.
  replace (sx^2+sy^2-2*rho*sx*sy) with
    ((sx-sy)*(sx-sy)+2*sx*sy*(1-rho)) by ring.
  exact (Rplus_le_le_0_compat _ _ Hs Hp).
Qed.

(** [iq_two_component_scale_concavity]
    Mathematical meaning: The equal-weight mean of two square-root scales is no larger than their root mean square.
    Exact representation: Two nonnegative scales a and b model the conditional residual scales of an equal-weight mixture.
    Premises and side conditions: Require a,b nonnegative; the inequality is stated on squared scales to avoid a redundant root monotonicity proof.
    Proof/definition method: Expand the deficit as a nonnegative squared difference.
    Library reuse: Stdlib Rle_0_sqr and lra/nra; no custom square lemma.
    Boundary: An algebraic two-component Jensen instance, not a general probability Jensen theorem. *)
Theorem iq_two_component_scale_concavity (a b : R) :
  ((a+b)/2)^2 <= (a^2+b^2)/2.
Proof.
  pose proof (Rle_0_sqr (a-b)) as H.
  unfold Rsqr in H.
  nra.
Qed.

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
  (* Normalize only the left side to the canonical lemma's notation.
     Avoid a reverse rewrite that also rewrites pooled_between on the right. *)
  replace (na*(a-pooled_mean na nb a b)^2+nb*(b-pooled_mean na nb a b)^2)
    with (na*(a-pooled_mean na nb a b)*(a-pooled_mean na nb a b)+
          nb*(b-pooled_mean na nb a b)*(b-pooled_mean na nb a b)) by ring.
  exact (pooled_between_centered_identity na nb a b Ha Hb).
Qed.

(** [iq_weighted_scale_jensen_deficit]
    Mathematical meaning: A mixture's squared mean residual scale differs
    from its mean squared scale by exactly the weighted dispersion.
    Exact representation: Bernoulli-weighted two-point variance identity.
    Premises and side conditions: Algebra holds for all real inputs;
    statistical interpretation requires weights in [0,1] and positive scales.
    Proof/definition method: Normalize the polynomial with Stdlib ring.
    Library reuse: Stdlib ring; centered-variance principle from pooling.
    Boundary: Does not establish the Gaussian absolute moment itself. *)
Theorem iq_weighted_scale_jensen_deficit (w a b : R) :
  w*a^2+(1-w)*b^2-(w*a+(1-w)*b)^2 =
  w*(1-w)*(a-b)^2.
Proof. ring. Qed.

(** [iq_weighted_scale_jensen_strict]
    Mathematical meaning: Distinct conditional scales and positive mixture
    weights yield a strictly smaller squared mean scale than mean square.
    Exact representation: Strict two-point Jensen inequality for scales.
    Premises and side conditions: Interior weight and distinct scales.
    Proof/definition method: Reuse weighted deficit and explicit positive
    square and product lemmas from the standard library.
    Library reuse: iq_weighted_scale_jensen_deficit, Rle_0_sqr,
    Rmult_integral, Rmult_lt_0_compat.
    Boundary: Algebraic non-identification certificate, not a theorem
    about probability measures or Gaussian absolute moments. *)
Theorem iq_weighted_scale_jensen_strict (w a b : R) :
  0 < w -> w < 1 -> a <> b ->
  (w*a+(1-w)*b)^2 < w*a^2+(1-w)*b^2.
Proof.
  intros Hw Hw1 Hne.
  pose proof (Rle_0_sqr (a-b)) as Hsq.
  unfold Rsqr in Hsq.
  assert (Hnz : (a-b)*(a-b) <> 0).
  { intro Hz. apply Rmult_integral in Hz.
    destruct Hz; apply Hne; lra. }
  assert (Hs : 0 < (a-b)*(a-b)) by lra.
  assert (Hweight : 0 < w*(1-w)).
  { apply Rmult_lt_0_compat; lra. }
  pose proof (Rmult_lt_0_compat _ _ Hweight Hs) as Hpositive.
  pose proof (iq_weighted_scale_jensen_deficit w a b) as Hidentity.
  nra.
Qed.


(** [iq_extrema] (definition).
    Mathematical meaning: Attained lower and upper endpoints of a finite
    battery, including repeated values at distinct test positions.
    Exact representation: Both endpoints occur and bound every listed value.
    Premises and side conditions: The empty list cannot satisfy this predicate.
    Proof/definition method: Use the standard list membership predicate.
    Library reuse: Stdlib List.In and real order.
    Boundary: Deterministic finite battery, not measurability or a distribution. *)
Definition iq_extrema (xs : list R) (lo hi : R) : Prop :=
  In lo xs /\ In hi xs /\
  (forall z, In z xs -> lo <= z /\ z <= hi).

(** [iq_extrema_exist].
    Mathematical meaning: Every nonempty finite battery attains both extremes.
    Exact proposition: A nonempty list has endpoints satisfying iq_extrema.
    Premises and side conditions: Nonempty list; arbitrary real scores.
    Proof/definition method: Induct on the list and compare the head with
    each attained endpoint of the tail.
    Library reuse: Stdlib List.In, Rle_dec and lra.
    Boundary: Pointwise existence; no random-variable measurability follows. *)
Theorem iq_extrema_exist (xs : list R) :
  xs <> [] -> exists lo hi, iq_extrema xs lo hi.
Proof.
  induction xs as [|a xs IH]; intro Hnonempty.
  - contradiction.
  - destruct xs as [|b ys].
    + exists a, a. unfold iq_extrema. simpl.
      split; [auto|]. split; [auto|].
      intros z [Hz|Hz]; [subst z; split; lra|contradiction].
    + assert (Htail : b :: ys <> []) by discriminate.
      destruct (IH Htail) as [lo [hi [Hlo [Hhi Hbounds]]]].
      assert (Horder : lo <= hi) by (destruct (Hbounds lo Hlo); assumption).
      simpl in Hlo, Hhi.
      destruct (Rle_dec a lo) as [Hal|Hal];
        destruct (Rle_dec hi a) as [Hha|Hha];
        [exists a, a|exists a, hi|exists lo, a|exists lo, hi];
        unfold iq_extrema; split; [simpl; tauto|];
        split; [simpl; tauto|]; intros z Hz;
        simpl in Hz; destruct Hz as [Hz|Hz].
      all: try (subst z; split; lra).
      all: destruct (Hbounds z Hz) as [Hlower Hupper]; split; lra.
Qed.

(** [iq_extrema_unique].
    Mathematical meaning: Numerical extrema are unique even when several
    positions realize an endpoint.
    Exact proposition: Two endpoint pairs of the same list agree.
    Premises and side conditions: Both pairs satisfy iq_extrema.
    Proof/definition method: Apply each pair's bounds to the other's members.
    Library reuse: Stdlib real order and lra.
    Boundary: Does not establish unique minimizing indices. *)
Theorem iq_extrema_unique (xs : list R) (lo hi lo' hi' : R) :
  iq_extrema xs lo hi -> iq_extrema xs lo' hi' ->
  lo = lo' /\ hi = hi'.
Proof.
  intros [Hl [Hh Hb]] [Hl' [Hh' Hb']].
  destruct (Hb lo' Hl') as [H1 _].
  destruct (Hb hi' Hh') as [_ H2].
  destruct (Hb' lo Hl) as [H3 _].
  destruct (Hb' hi Hh) as [_ H4].
  split; lra.
Qed.

(** [iq_extrema_affine].
    Mathematical meaning: Translation and nonnegative scaling preserve
    extrema, including zero scale and repeated values.
    Exact proposition: Affine images of the endpoints are extrema of
    the corresponding mapped list.
    Premises and side conditions: Nonnegative scale and attained extrema.
    Proof/definition method: Transport membership through map and multiply
    the lower and upper bounds by the nonnegative scalar.
    Library reuse: Stdlib in_map_iff, Rmult_le_compat_l and lra.
    Boundary: Pointwise part of the Gaussian range representation. *)
Theorem iq_extrema_affine (xs : list R) (lo hi a s : R) :
  0 <= s -> iq_extrema xs lo hi ->
  iq_extrema (map (fun z => a+s*z) xs) (a+s*lo) (a+s*hi).
Proof.
  intros Hs [Hl [Hh Hb]].
  unfold iq_extrema.
  split.
  - apply in_map_iff. exists lo. split; [reflexivity|exact Hl].
  - split.
    + apply in_map_iff. exists hi. split; [reflexivity|exact Hh].
    + intros z Hz. apply in_map_iff in Hz.
      destruct Hz as [x [Heq Hx]]. subst z.
      destruct (Hb x Hx) as [Hlx Hxh].
      pose proof (Rmult_le_compat_l s lo x Hs Hlx) as H1.
      pose proof (Rmult_le_compat_l s x hi Hs Hxh) as H2.
      split; lra.
Qed.

(** [iq_extrema_nested_range].
    Mathematical meaning: Adding observations cannot shrink a realized range.
    Exact proposition: List inclusion and attained extrema imply ordered
    maximum-minus-minimum differences.
    Premises and side conditions: Each list has attained endpoints;
    inclusion need not preserve multiplicities.
    Proof/definition method: Use the larger list's bounds on both smaller
    list endpoint witnesses.
    Library reuse: Stdlib List.incl and lra.
    Boundary: The nested iid coupling and expectation monotonicity are separate. *)
Theorem iq_extrema_nested_range (xs ys : list R) (lo hi lo' hi' : R) :
  incl xs ys -> iq_extrema xs lo hi -> iq_extrema ys lo' hi' ->
  hi-lo <= hi'-lo'.
Proof.
  intros Hinc [Hl [Hh Hb]] [Hl' [Hh' Hb']].
  destruct (Hb' lo (Hinc lo Hl)) as [H1 _].
  destruct (Hb' hi (Hinc hi Hh)) as [_ H2].
  lra.
Qed.

(** [iq_pair_gaps] (definition).
    Mathematical meaning: Enumerate one signed difference for every pair
    of distinct list positions i<j, retaining multiplicities.
    Exact representation: Pair the head with each tail position via map,
    then append the recursively enumerated tail differences.
    Premises and side conditions: Any finite list of real scores.
    Proof/definition method: Structural recursion using standard map and app.
    Library reuse: Stdlib List.map and List.app; shared finite_sum for sums.
    Boundary: Signed values may repeat or vanish; no deduplication. *)
Fixpoint iq_pair_gaps (xs : list R) : list R :=
  match xs with
  | [] => []
  | a :: tail => map (fun z => a-z) tail ++ iq_pair_gaps tail
  end.

(** [iq_pair_gaps_contains_distinct].
    Mathematical meaning: Two distinct attained scores produce a listed
    pair difference, possibly with the opposite orientation.
    Exact proposition: Distinct members x,y yield x-y or y-x in iq_pair_gaps.
    Premises and side conditions: Both values occur and differ.
    Proof/definition method: Induct on positions; head-tail pairs use map,
    tail-tail pairs reuse the induction hypothesis.
    Library reuse: Stdlib in_map_iff, in_or_app and List.In.
    Boundary: A value-based witness; equal-valued positions are also
    enumerated but are not needed in this theorem. *)
Theorem iq_pair_gaps_contains_distinct (xs : list R) (x y : R) :
  x <> y -> In x xs -> In y xs ->
  In (x-y) (iq_pair_gaps xs) \/ In (y-x) (iq_pair_gaps xs).
Proof.
  induction xs as [|a xs IH]; intros Hne Hx Hy.
  - contradiction.
  - simpl in Hx, Hy.
    cbn [iq_pair_gaps].
    destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
    + exfalso. apply Hne. congruence.
    + subst x. left. apply in_or_app. left.
      apply in_map_iff. exists y. split; [reflexivity|exact Hy].
    + subst y. right. apply in_or_app. left.
      apply in_map_iff. exists x. split; [reflexivity|exact Hx].
    + destruct (IH Hne Hx Hy) as [H|H].
      * left. apply in_or_app. right. exact H.
      * right. apply in_or_app. right. exact H.
Qed.

(** [iq_extrema_pair_square_bound].
    Mathematical meaning: A realized squared range is bounded by the
    sum of squared gaps over all unordered pairs of distinct positions.
    Exact proposition: For attained extrema, the squared endpoint
    difference is no larger than the finite_sum of squares of iq_pair_gaps.
    Premises and side conditions: Attained extrema; includes constant lists
    and singletons, for which the range is zero.
    Proof/definition method: For equal endpoints use nonnegativity.
    Otherwise the endpoint gap occurs up to sign; reuse the member bound.
    Library reuse: iq_pair_gaps_contains_distinct, iq_range_pair_square_bound,
    FiniteSum.finite_sum_nonnegative, Stdlib ring and nra.
    Boundary: Deterministic inequality of prop:bound; expectation and
    Cauchy-Schwarz on an actual probability space remain separate. *)
Theorem iq_extrema_pair_square_bound (xs : list R) (lo hi : R) :
  iq_extrema xs lo hi ->
  (hi-lo)*(hi-lo) <= finite_sum (fun d => d*d) (iq_pair_gaps xs).
Proof.
  intros [Hl [Hh Hb]].
  destruct (Req_EM_T hi lo) as [Heq|Hne].
  - subst hi. replace ((lo-lo)*(lo-lo)) with 0 by ring.
    apply finite_sum_nonnegative. intros d Hd. nra.
  - destruct (iq_pair_gaps_contains_distinct xs hi lo Hne Hh Hl) as [H|H].
    + exact (iq_range_pair_square_bound (iq_pair_gaps xs) (hi-lo) H).
    + replace ((hi-lo)*(hi-lo)) with ((lo-hi)*(lo-hi)) by ring.
      exact (iq_range_pair_square_bound (iq_pair_gaps xs) (lo-hi) H).
Qed.

(** [iq_extrema_range_attains_pair_max].
    Mathematical meaning: No pair has larger squared gap than the range;
    the attained endpoints themselves realize that squared gap.
    Exact proposition: Any two members have squared difference at most
    the squared endpoint difference.
    Premises and side conditions: Both endpoints and both scores are members.
    Proof/definition method: Bound both signs of the difference by the range
    and use nonnegativity of the product of complementary differences.
    Library reuse: Stdlib real order, Rmult_le_pos, ring and nra.
    Boundary: Deterministic finite-range identity only. *)
Theorem iq_extrema_range_attains_pair_max (xs : list R) (lo hi x y : R) :
  iq_extrema xs lo hi -> In x xs -> In y xs ->
  (x-y)*(x-y) <= (hi-lo)*(hi-lo).
Proof.
  intros [Hl [Hh Hb]] Hx Hy.
  destruct (Hb x Hx) as [Hlx Hxh].
  destruct (Hb y Hy) as [Hly Hyh].
  assert (Hp : 0 <= ((hi-lo)-(x-y))*((hi-lo)+(x-y))).
  { apply Rmult_le_pos; lra. }
  nra.
Qed.
