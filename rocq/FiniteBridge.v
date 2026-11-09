(** Module: FiniteBridge.v
   Purpose: Checked interpretation between Boolean event mass and finite moments.
   Connects FiniteUnion event indicators to FiniteMoments expectation, variance, covariance and algebraic independence conditions, including positive-event filtering and explicitly normalized conditional weights.
   Mathematical representation: Both imported models use the same FiniteSum fold, and Boolean true/false indicators are represented by real 1/0.
   Explicit hypotheses: Probability interpretations require normalized nonnegative weights; algebraic equalities may hold for any real weights.
   Library use: FiniteSum, FiniteUnion, FiniteMoments and Rocq's Bool/Reals tactics.
   Limitations: Zero indicator covariance corresponds to a finite event product identity, not statistical independence for arbitrary continuous distributions.
   Proof documentation: Every public and helper declaration below has its
   own statement, hypothesis, proof-approach, and scope commentary.
   Reproduction: rocq compile FiniteBridge.v (after imported local modules);
   see rocq/README.md and rocq/LIBRARY_AUDIT.md for dependency order,
   checked-claim mapping, and library audit. All results are Rocq-kernel
   checked; no unchecked evidence is created by comments.
 *)
(* Bridge between the finite-event model and the finite-moment model.
   Both are interpreted with the shared Stdlib.List-based finite sum.
   The bridge does not assume independence, a measure axiom, or normality. *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import FiniteSum FiniteUnion FiniteMoments.
Import ListNotations.
Open Scope R_scope.

(**
   [finite_sum_models_agree] (theorem) — Correspondence between finite event
   probabilities and score moments.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem finite_sum_models_agree : forall (A : Type)
   (samples : list A) (f : A -> R), @FiniteUnion.finite_sum A f samples =
   @FiniteMoments.sum_finite A f samples.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses definitional reduction.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_sum_models_agree :
  forall (A : Type) (samples : list A) (f : A -> R),
    @FiniteUnion.finite_sum A f samples =
      @FiniteMoments.sum_finite A f samples.
Proof.
  reflexivity.
Qed.

(**
   [finite_total_mass_models_agree] (theorem) — Correspondence between finite event
   probabilities and score moments.
   Mathematical meaning: Expresses a checked identity or bound within the
   correspondence between finite event probabilities and score moments.
   Exact checked proposition: Theorem finite_total_mass_models_agree : forall (A :
   Type) (samples : list A) (weight : A -> R), @FiniteMoments.total_mass A samples
   weight = @FiniteUnion.finite_sum A weight samples.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses definitional reduction.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_total_mass_models_agree :
  forall (A : Type) (samples : list A) (weight : A -> R),
    @FiniteMoments.total_mass A samples weight =
      @FiniteUnion.finite_sum A weight samples.
Proof.
  reflexivity.
Qed.

(**
   [finite_event_probability_is_indicator_expectation] (theorem) — Correspondence
   between finite event probabilities and score moments.
   Mathematical meaning: The weighted mass assigned to a Boolean event is literally
   the finite expectation of the event's 0-1 indicator score. This
   identifies the event and score-model representations of one
   and the same list-fold quantity, with duplicate occurrences intact.
   Exact checked proposition: Theorem
   finite_event_probability_is_indicator_expectation : forall (A : Type) (samples :
   list A) (weight : A -> R) (event : A -> bool), @FiniteUnion.finite_prob A weight
   samples event = @FiniteMoments.expect A samples weight (fun x =>
   FiniteUnion.indicator (event x)).
   Premises and side conditions: Arbitrary finite outcome list, real weights and total
   Boolean event predicates. No positivity, mass-one or independence
   premise is used for the identity; a genuine probability
   interpretation requires a nonnegative normalized sample mass.
   Proof/definition method: Both module definitions expand to the same
   FiniteSum.finite_sum of weight times indicator, so Rocq's
   definitional equality establishes the theorem immediately.
   Library reuse: FiniteUnion.finite_prob, FiniteMoments.expect,
   FiniteSum.finite_sum, Stdlib.List.map/fold_right and Bool.
   Boundary: Identity of finite weighted list representations, not a
   construction of a conditional expectation, a countably additive
   measure, or a proof of empirical psychometric quantities.
*)
Theorem finite_event_probability_is_indicator_expectation :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (event : A -> bool),
    @FiniteUnion.finite_prob A weight samples event =
      @FiniteMoments.expect A samples weight
        (fun x => FiniteUnion.indicator (event x)).
Proof.
  reflexivity.
Qed.

(* A Boolean selection of sample occurrences is encoded by a
   conjunction in the indicator score.  The event-to-moment bridge and
   filtered-sample identity already establish this without constructing
   a new weighted expectation or a conditional probability measure. *)
(**
   [filtered_event_mass_is_indicator_expectation] (theorem) — A filtered
   finite event mass as a score expectation on the original sample.
   Mathematical meaning: Selecting occurrences with a Boolean
   predicate and measuring an event gives exactly the original
   sample's expectation of the indicator of their intersection.
   Exact checked proposition: forall A samples weight selection event,
   FiniteUnion.finite_prob weight (filter selection samples) event =
   FiniteMoments.expect samples weight
   (fun x => FiniteUnion.indicator (andb (selection x) (event x))).
   Premises and side conditions: The sample is an arbitrary finite
   list, with multiplicities and arbitrary real weights preserved.
   No normalization or independence hypothesis is needed for this
   algebraic identity, though such assumptions are needed to
   interpret the mass as a probability distribution.
   Proof/definition method: Apply the existing
   FiniteUnion.finite_prob_on_filtered_samples theorem, then the
   already checked event-to-indicator-expectation bridge.
   Library reuse: Stdlib.List.filter, Stdlib.Bool.andb,
   FiniteUnion.finite_prob_on_filtered_samples and
   finite_event_probability_is_indicator_expectation.
   Boundary: Exact finite-list identity, not a definition of
   continuous conditional expectation or empirical score validity.
 *)
Theorem filtered_event_mass_is_indicator_expectation :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (selection event : A -> bool),
    @FiniteUnion.finite_prob A weight
      (filter selection samples) event =
    @FiniteMoments.expect A samples weight
      (fun x => FiniteUnion.indicator
        (andb (selection x) (event x))).
Proof.
  intros A samples weight selection event.
  rewrite (@FiniteUnion.finite_prob_on_filtered_samples
    A weight samples selection event).
  apply finite_event_probability_is_indicator_expectation.
Qed.

(* Finite families of events use Stdlib.List.existsb.  Applying the
   same established indicator bridge avoids a second event-family
   induction or a parallel finite-moment representation. *)
(**
   [filtered_union_mass_is_indicator_expectation] (theorem) — A finite
   event-family union after sample selection as an indicator moment.
   Mathematical meaning: The union mass after selecting sample
   occurrences equals the original finite expected indicator of
   selection AND membership in at least one listed event.
   Exact checked proposition: forall A samples weight selection events,
   FiniteUnion.union_prob weight (filter selection samples) events =
   FiniteMoments.expect samples weight
   (fun x => FiniteUnion.indicator
     (andb (selection x) (FiniteUnion.any_event events x))).
   Premises and side conditions: Event families are finite Boolean
   predicate lists and may overlap or contain duplicates. Weights
   can be signed and need not sum to one; no event independence or
   distinctness is required for equality.
   Proof/definition method: Rewrite with the previously checked
   union_prob_on_filtered_samples identity and then invoke the
   finite_event_probability_is_indicator_expectation bridge.
   Library reuse: Stdlib.List.existsb and filter,
   Stdlib.Bool.andb, FiniteUnion.union_prob_on_filtered_samples,
   and the previously proven indicator-expectation correspondence.
   Boundary: No empirical admission data, Gaussian assumptions,
   continuous measure construction or normalized conditioning.
 *)
Theorem filtered_union_mass_is_indicator_expectation :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (selection : A -> bool) (events : list (A -> bool)),
    @FiniteUnion.union_prob A weight
      (filter selection samples) events =
    @FiniteMoments.expect A samples weight
      (fun x => FiniteUnion.indicator
        (andb (selection x) (@FiniteUnion.any_event A events x))).
Proof.
  intros A samples weight selection events.
  rewrite (@FiniteUnion.union_prob_on_filtered_samples
    A weight samples selection events).
  apply finite_event_probability_is_indicator_expectation.
Qed.

(**
   [indicator_square] (lemma) — Correspondence between finite event probabilities and
   score moments.
   Mathematical meaning: Establishes a correlation, square-root or reliability
   identity under the stated real-number constraints.
   Exact checked proposition: Lemma indicator_square : forall b,
   FiniteUnion.indicator b * FiniteUnion.indicator b = FiniteUnion.indicator b.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization; references
   include FiniteUnion.indicator.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Lemma indicator_square :
  forall b,
    FiniteUnion.indicator b * FiniteUnion.indicator b =
      FiniteUnion.indicator b.
Proof.
  intros []; unfold FiniteUnion.indicator; ring.
Qed.

(**
   [indicator_product_and] (lemma) — Correspondence between finite event
   probabilities and score moments.
   Mathematical meaning: Expresses a checked identity or bound within the
   correspondence between finite event probabilities and score moments.
   Exact checked proposition: Lemma indicator_product_and : forall b c,
   FiniteUnion.indicator b * FiniteUnion.indicator c = FiniteUnion.indicator (andb b
   c).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses ring/field normalization, definitional
   reduction; references include FiniteUnion.indicator.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Lemma indicator_product_and :
  forall b c,
    FiniteUnion.indicator b * FiniteUnion.indicator c =
      FiniteUnion.indicator (andb b c).
Proof.
  intros [] []; unfold FiniteUnion.indicator; simpl; ring.
Qed.

(**
   [finite_event_indicator_variance] (theorem) — Correspondence between finite event
   probabilities and score moments.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem finite_event_indicator_variance : forall (A :
   Type) (samples : list A) (weight : A -> R) (event : A -> bool),
   @FiniteMoments.variance A samples weight (fun x => FiniteUnion.indicator (event
   x)) = @FiniteUnion.finite_prob A weight samples event * (1 -
   @FiniteUnion.finite_prob A weight samples event).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   FiniteMoments.expectation_ext., indicator_square., Hsquare..
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_event_indicator_variance :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (event : A -> bool),
    @FiniteMoments.variance A samples weight
      (fun x => FiniteUnion.indicator (event x)) =
    @FiniteUnion.finite_prob A weight samples event *
      (1 - @FiniteUnion.finite_prob A weight samples event).
Proof.
  intros A samples weight event.
  rewrite (@FiniteMoments.variance_second_moment A samples weight
    (fun x => FiniteUnion.indicator (event x))).
  assert (Hsquare :
    @FiniteMoments.expect A samples weight
      (fun x => FiniteUnion.indicator (event x) *
                FiniteUnion.indicator (event x)) =
    @FiniteMoments.expect A samples weight
      (fun x => FiniteUnion.indicator (event x))).
  { apply FiniteMoments.expectation_ext.
    intro x; apply indicator_square. }
  rewrite Hsquare.
  rewrite <- (finite_event_probability_is_indicator_expectation
    A samples weight event).
  ring.
Qed.

(**
   [finite_event_indicator_covariance] (theorem) — Correspondence between finite
   event probabilities and score moments.
   Mathematical meaning: The covariance of two Boolean indicator scores is
   the mass of their conjunction minus the product of their
   individual masses, the exact algebraic independence residual.
   Exact checked proposition: Theorem finite_event_indicator_covariance : forall (A :
   Type) (samples : list A) (weight : A -> R) (a b : A -> bool),
   @FiniteMoments.covariance A samples weight (fun x => FiniteUnion.indicator (a x))
   (fun x => FiniteUnion.indicator (b x)) = @FiniteUnion.finite_prob A weight samples
   (fun x => andb (a x) (b x)) - @FiniteUnion.finite_prob A weight samples a *
   @FiniteUnion.finite_prob A weight samples b.
   Premises and side conditions: No mass normalization, positive weights or independence
   assumption is needed to establish the formula: all quantities
   are finite real-valued list sums. If the weights do define a
   probability measure, the residual has its conventional meaning.
   Proof/definition method: Unfold the existing finite covariance definition,
   rewrite each indicator expectation via the event-mass bridge,
   and use indicator_product_and to identify the product score
   with the conjunction indicator.
   Library reuse: FiniteMoments.covariance and expectation_ext,
   finite_event_probability_is_indicator_expectation,
   indicator_product_and, Stdlib.Bool.andb, Stdlib.Reals.
   Boundary: No inference about actual events in population data;
   zero algebraic covariance only represents probabilistic
   independence once a valid finite probability law is supplied.
*)
Theorem finite_event_indicator_covariance :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (a b : A -> bool),
    @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => FiniteUnion.indicator (b x)) =
      @FiniteUnion.finite_prob A weight samples
        (fun x => andb (a x) (b x)) -
      @FiniteUnion.finite_prob A weight samples a *
        @FiniteUnion.finite_prob A weight samples b.
Proof.
  intros A samples weight a b.
  unfold FiniteMoments.covariance.
  assert (Hproduct :
    @FiniteMoments.expect A samples weight
      (fun x => FiniteUnion.indicator (a x) *
                FiniteUnion.indicator (b x)) =
    @FiniteMoments.expect A samples weight
      (fun x => FiniteUnion.indicator (andb (a x) (b x)))).
  { apply FiniteMoments.expectation_ext.
    intro x; apply indicator_product_and. }
  rewrite Hproduct.
  rewrite <- (finite_event_probability_is_indicator_expectation
    A samples weight (fun x => andb (a x) (b x))).
  rewrite <- (finite_event_probability_is_indicator_expectation
    A samples weight a).
  rewrite <- (finite_event_probability_is_indicator_expectation
    A samples weight b).
  reflexivity.
Qed.

(**
   [finite_event_independence_iff_zero_indicator_covariance] (theorem) —
   Correspondence between finite event probabilities and score moments.
   Mathematical meaning: The factorization equation P(a AND b) = P(a)P(b)
   is equivalent to zero covariance between the two 0-1 indicator
   scores in this finite weighted event model.
   Exact checked proposition: Theorem
   finite_event_independence_iff_zero_indicator_covariance : forall (A : Type)
   (samples : list A) (weight : A -> R) (a b : A -> bool), @FiniteMoments.covariance
   A samples weight (fun x => FiniteUnion.indicator (a x)) (fun x =>
   FiniteUnion.indicator (b x)) = 0 <-> @FiniteUnion.finite_prob A weight samples
   (fun x => andb (a x) (b x)) = @FiniteUnion.finite_prob A weight samples a *
   @FiniteUnion.finite_prob A weight samples b.
   Premises and side conditions: Holds algebraically for arbitrary real weights,
   even if the weighted lists do not define probabilities. For
   the biconditional to be read as stochastic independence, the
   weights must be nonnegative and normalized over the sample.
   Proof/definition method: Rewrite covariance via
   finite_event_indicator_covariance and solve the resulting
   exact real equality with Rocq's Stdlib.Lra tactic.
   Library reuse: finite_event_indicator_covariance, Stdlib.Bool.andb,
   Stdlib.Reals and Stdlib.Lra; no independence axiom is invoked.
   Boundary: Only independence of the two finite Boolean events
   is characterized. Zero covariance of arbitrary real-valued
   scores does not generally imply their statistical independence.
*)
Theorem finite_event_independence_iff_zero_indicator_covariance :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (a b : A -> bool),
    @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => FiniteUnion.indicator (b x)) = 0 <->
      @FiniteUnion.finite_prob A weight samples
        (fun x => andb (a x) (b x)) =
      @FiniteUnion.finite_prob A weight samples a *
        @FiniteUnion.finite_prob A weight samples b.
Proof.
  intros A samples weight a b.
  rewrite finite_event_indicator_covariance.
  split; intro H; lra.
Qed.

(**
   [finite_event_indicator_zero_variance_iff_extreme_mass] (theorem) — Correspondence
   between finite event probabilities and score moments.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem
   finite_event_indicator_zero_variance_iff_extreme_mass : forall (A : Type) (samples
   : list A) (weight : A -> R) (event : A -> bool), @FiniteMoments.variance A samples
   weight (fun x => FiniteUnion.indicator (event x)) = 0 <-> @FiniteUnion.finite_prob
   A weight samples event = 0 \/ @FiniteUnion.finite_prob A weight samples event = 1.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions; stated unit-variance conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, linear real arithmetic (Lra), ring/field
   normalization; references include finite_event_indicator_variance.,
   Rmult_integral.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_event_indicator_zero_variance_iff_extreme_mass :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (event : A -> bool),
    @FiniteMoments.variance A samples weight
      (fun x => FiniteUnion.indicator (event x)) = 0 <->
      @FiniteUnion.finite_prob A weight samples event = 0 \/
      @FiniteUnion.finite_prob A weight samples event = 1.
Proof.
  intros A samples weight event.
  rewrite finite_event_indicator_variance.
  split.
  - intro H.
    apply Rmult_integral in H.
    destruct H as [H | H].
    + left; exact H.
    + right; lra.
  - intros [H | H]; rewrite H; ring.
Qed.

(* Completing the square yields this universal Bernoulli bound.  It
   is an algebraic upper bound, not a claim that arbitrary signed weights
   define a probability distribution. *)
(**
   [finite_event_indicator_variance_at_most_quarter] (theorem) — Correspondence
   between finite event probabilities and score moments.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem finite_event_indicator_variance_at_most_quarter
   : forall (A : Type) (samples : list A) (weight : A -> R) (event : A -> bool),
   @FiniteMoments.variance A samples weight (fun x => FiniteUnion.indicator (event
   x)) <= /4.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, polynomial real arithmetic (Psatz); references
   include finite_event_indicator_variance., Rle_0_sqr..
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_event_indicator_variance_at_most_quarter :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (event : A -> bool),
    @FiniteMoments.variance A samples weight
      (fun x => FiniteUnion.indicator (event x)) <= /4.
Proof.
  intros A samples weight event.
  rewrite finite_event_indicator_variance.
  set (p := @FiniteUnion.finite_prob A weight samples event).
  assert (Hsquare : 0 <= Rsqr (p - /2)) by apply Rle_0_sqr.
  unfold Rsqr in Hsquare.
  nra.
Qed.

(* Complement variance requires a normalized finite total mass. *)
(**
   [finite_event_indicator_complement_variance] (theorem) — Correspondence between
   finite event probabilities and score moments.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem finite_event_indicator_complement_variance :
   forall (A : Type) (samples : list A) (weight : A -> R) (event : A -> bool),
   @FiniteMoments.total_mass A samples weight = 1 -> @FiniteMoments.variance A
   samples weight (fun x => FiniteUnion.indicator (negb (event x))) =
   @FiniteMoments.variance A samples weight (fun x => FiniteUnion.indicator (event
   x)).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_event_indicator_complement_variance :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (event : A -> bool),
    @FiniteMoments.total_mass A samples weight = 1 ->
    @FiniteMoments.variance A samples weight
      (fun x => FiniteUnion.indicator (negb (event x))) =
    @FiniteMoments.variance A samples weight
      (fun x => FiniteUnion.indicator (event x)).
Proof.
  intros A samples weight event Hmass.
  rewrite !finite_event_indicator_variance.
  rewrite (@FiniteUnion.normalized_finite_prob_complement
    A weight samples event Hmass).
  ring.
Qed.

(* Use established covariance extensionality, affine-shift
   invariance and homogeneity; avoid re-expanding finite sums. *)
(**
   [finite_event_indicator_covariance_complement_second] (theorem) — Correspondence
   between finite event probabilities and score moments.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   finite_event_indicator_covariance_complement_second : forall (A : Type) (samples :
   list A) (weight : A -> R) (a b : A -> bool), @FiniteMoments.total_mass A samples
   weight = 1 -> @FiniteMoments.covariance A samples weight (fun x =>
   FiniteUnion.indicator (a x)) (fun x => FiniteUnion.indicator (negb (b x))) = -
   @FiniteMoments.covariance A samples weight (fun x => FiniteUnion.indicator (a x))
   (fun x => FiniteUnion.indicator (b x)).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, ring/field normalization, definitional
   reduction; references include FiniteMoments.covariance_extensional..
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_event_indicator_covariance_complement_second :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (a b : A -> bool),
    @FiniteMoments.total_mass A samples weight = 1 ->
    @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => FiniteUnion.indicator (negb (b x))) =
    - @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => FiniteUnion.indicator (b x)).
Proof.
  intros A samples weight a b Hmass.
  transitivity
    (@FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => (-1) * FiniteUnion.indicator (b x) + 1)).
  - apply FiniteMoments.covariance_extensional.
    + intro x; reflexivity.
    + intro x; destruct (b x); simpl; ring.
  - rewrite (@FiniteMoments.covariance_invariant_under_second_shift
      A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => (-1) * FiniteUnion.indicator (b x)) 1 Hmass).
    rewrite (@FiniteMoments.covariance_scale_second
      A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => FiniteUnion.indicator (b x)) (-1)).
    ring.
Qed.

(**
   [finite_event_indicator_covariance_complement_first] (theorem) — Correspondence
   between finite event probabilities and score moments.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   finite_event_indicator_covariance_complement_first : forall (A : Type) (samples :
   list A) (weight : A -> R) (a b : A -> bool), @FiniteMoments.total_mass A samples
   weight = 1 -> @FiniteMoments.covariance A samples weight (fun x =>
   FiniteUnion.indicator (negb (a x))) (fun x => FiniteUnion.indicator (b x)) = -
   @FiniteMoments.covariance A samples weight (fun x => FiniteUnion.indicator (a x))
   (fun x => FiniteUnion.indicator (b x)).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include
   finite_event_indicator_covariance_complement_second., Hmass..
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_event_indicator_covariance_complement_first :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (a b : A -> bool),
    @FiniteMoments.total_mass A samples weight = 1 ->
    @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (negb (a x)))
      (fun x => FiniteUnion.indicator (b x)) =
    - @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => FiniteUnion.indicator (b x)).
Proof.
  intros A samples weight a b Hmass.
  rewrite (@FiniteMoments.covariance_symmetric
    A samples weight
    (fun x => FiniteUnion.indicator (negb (a x)))
    (fun x => FiniteUnion.indicator (b x))).
  rewrite (@FiniteMoments.covariance_symmetric
    A samples weight
    (fun x => FiniteUnion.indicator (a x))
    (fun x => FiniteUnion.indicator (b x))).
  apply finite_event_indicator_covariance_complement_second.
  exact Hmass.
Qed.

(**
   [finite_event_indicator_covariance_complement_both] (theorem) — Correspondence
   between finite event probabilities and score moments.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   finite_event_indicator_covariance_complement_both : forall (A : Type) (samples :
   list A) (weight : A -> R) (a b : A -> bool), @FiniteMoments.total_mass A samples
   weight = 1 -> @FiniteMoments.covariance A samples weight (fun x =>
   FiniteUnion.indicator (negb (a x))) (fun x => FiniteUnion.indicator (negb (b x)))
   = @FiniteMoments.covariance A samples weight (fun x => FiniteUnion.indicator (a
   x)) (fun x => FiniteUnion.indicator (b...
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include
   finite_event_indicator_covariance_complement_first,
   finite_event_indicator_covariance_complement_second.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
 *)
Theorem finite_event_indicator_covariance_complement_both :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (a b : A -> bool),
    @FiniteMoments.total_mass A samples weight = 1 ->
    @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (negb (a x)))
      (fun x => FiniteUnion.indicator (negb (b x))) =
    @FiniteMoments.covariance A samples weight
      (fun x => FiniteUnion.indicator (a x))
      (fun x => FiniteUnion.indicator (b x)).
Proof.
  intros A samples weight a b Hmass.
  rewrite (finite_event_indicator_covariance_complement_first
    A samples weight a (fun x => negb (b x)) Hmass).
  rewrite (finite_event_indicator_covariance_complement_second
    A samples weight a b Hmass).
  ring.
Qed.


(**
   [finite_normalized_conditional_independence_iff_zero_indicator_covariance] (theorem) — The same finite independence assertion in event and moment form.
   Mathematical meaning: Under unit total sample weight, conditional independence of two finite Boolean events given the certain event is equivalent to zero covariance of their two real-valued 0–1 indicator scores. This is a bridge between the established finite event and finite moment representations.
   Exact checked proposition: For any type A, sample list, real weight function and Boolean events a and b, FiniteUnion.finite_sum weight samples=1 implies finite_conditional_independent weight samples a b (fun _ => true) iff FiniteMoments.covariance of the a and b indicator scores is zero.
   Premises and side conditions: Total enumerated weight must be exactly one, so that conditioning on true has positive mass and reduces to unconditioned finite event mass. Nonnegative weights are required for probability interpretation, but not for the purely algebraic equivalence. Duplicate sample occurrences count separately.
   Proof/definition method: Apply the previously verified normalized true-conditioning product equivalence, followed by the established finite indicator covariance/product equivalence; merely reverse the iff orientation, with no new variance algebra or list traversal.
   Library reuse: FiniteUnion.finite_conditional_independent_given_true_iff_marginal_product, finite_event_independence_iff_zero_indicator_covariance and Stdlib.Logic. Reuse the common FiniteSum fold indirectly through existing model bridges.
   Boundary: Zero covariance characterizes factorization only for these Boolean indicator scores; it is not a general zero-covariance-implies-independence theorem for arbitrary scores or continuous distributions.
 *)
Theorem finite_normalized_conditional_independence_iff_zero_indicator_covariance :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (a b : A -> bool),
    @FiniteUnion.finite_sum A weight samples = 1 ->
    (@FiniteUnion.finite_conditional_independent A
       weight samples a b (fun _ => true) <->
     @FiniteMoments.covariance A samples weight
       (fun x => FiniteUnion.indicator (a x))
       (fun x => FiniteUnion.indicator (b x)) = 0).
Proof.
  intros A samples weight a b Hmass.
  rewrite (@FiniteUnion.finite_conditional_independent_given_true_iff_marginal_product
    A weight samples a b Hmass).
  pose proof (finite_event_independence_iff_zero_indicator_covariance
    A samples weight a b) as Hcriterion.
  split; intro H.
  - apply (proj2 Hcriterion); exact H.
  - apply (proj1 Hcriterion); exact H.
Qed.



(**
   [conditioned_weights] (definition) — Explicit normalization of a finite sample selected by a Boolean conditioning event.
   Mathematical meaning: When conditioning a weighted finite outcome list on a positive-mass Boolean event G, multiply every retained outcome's original weight by the reciprocal of the original mass P(G). The weighting function is defined on the entire outcome type, while the intended sample list is Stdlib.List.filter G samples.
   Exact declaration: conditioned_weights A weight samples given x := / (FiniteUnion.finite_prob weight samples given) * weight x, for an arbitrary outcome type A.
   Premises and side conditions: The definition itself is a total real expression even if the conditioning mass is zero, but the downstream probability theorem requires this mass to be strictly positive. Repeated sampled outcomes remain repeated and get their scaled original weights.
   Proof/definition method: Compose the existing finite event mass with Rocq's standard real reciprocal and scalar multiplication; there is no independent probability measure, list traversal or normalization algorithm.
   Library reuse: FiniteUnion.finite_prob, Stdlib.Reals.Rinv and Stdlib.List.filter for the associated restricted sample.
   Boundary: This is a finite exact mass normalization of a selected outcome list, not a continuous conditional-density construction or an arbitrary change of weights.
 *)
Definition conditioned_weights (A : Type) (weight : A -> R)
    (samples : list A) (given : A -> bool) : A -> R :=
  fun x => / (@FiniteUnion.finite_prob A weight samples given) * weight x.

(**
   [conditioned_weights_total_mass_one] (theorem) — Exact normalization of the Boolean-filtered finite sample.
   Mathematical meaning: The total original weight of the G-filtered outcome list is exactly the original event mass P(G), so division by that strictly positive mass makes the filtered list's total weight exactly one, even if the original complete sample was not normalized.
   Exact checked proposition: For arbitrary A, samples, weights and given, 0 < FiniteUnion.finite_prob weight samples given implies FiniteUnion.finite_sum (conditioned_weights A weight samples given) (filter given samples) = 1.
   Premises and side conditions: Strict positivity of the finite conditioning mass is required to cancel the reciprocal. Original total mass need not be one, and repeated sample occurrences retain their contributions; individual signed weights are permitted for the algebraic identity.
   Proof/definition method: Unfold only the shared finite-sum alias and the new scalar weight definition, pull out the constant reciprocal using FiniteSum.finite_sum_scale, identify filtered total mass with the existing finite_prob_as_filtered_mass, and cancel with Rocq's real field tactic.
   Library reuse: FiniteSum.finite_sum_scale, FiniteUnion.finite_prob_as_filtered_mass, Stdlib.List.filter, Stdlib.Reals field and Stdlib.Lra; no new summation or filtered-normalization recursion is implemented.
   Boundary: A unit total real mass is not by itself a probability measure when any original retained weight is negative; nonnegativity has a separate theorem.
 *)
Theorem conditioned_weights_total_mass_one :
  forall (A : Type) (samples : list A)
         (weight : A -> R) (given : A -> bool),
    0 < @FiniteUnion.finite_prob A weight samples given ->
    @FiniteUnion.finite_sum A
      (conditioned_weights A weight samples given)
      (filter given samples) = 1.
Proof.
  intros A samples weight given Hpositive.
  unfold conditioned_weights, FiniteUnion.finite_sum.
  rewrite (FiniteSum.finite_sum_scale (filter given samples)
    (/ (@FiniteUnion.finite_prob A weight samples given)) weight).
  rewrite <- (@FiniteUnion.finite_prob_as_filtered_mass
    A weight samples given).
  field; lra.
Qed.

(**
   [conditioned_weights_nonnegative_on_filtered_samples] (theorem) — Nonnegative conditional weights on retained sampled outcomes.
   Mathematical meaning: If the original finite samples carry nonnegative weights and the conditioning event has positive mass, the rescaled weights of each retained G-satisfying outcome remain nonnegative. Together with conditioned_weights_total_mass_one, the conditioned list is an explicitly normalized nonnegative finite probability model.
   Exact checked proposition: For any A, original samples, weight and given, positive original given mass and nonnegative original sampled weights imply 0 <= conditioned_weights A weight samples given x for every x in filter given samples.
   Premises and side conditions: Strict positivity of P(G) and nonnegativity of each weight on the original sample are explicit. No distinct-outcome assumption is needed and no positivity is demanded outside the selected finite sample.
   Proof/definition method: Use Stdlib.List.filter_In to recover original-sample membership, Stdlib.Reals.Rinv_0_lt_compat for the positive normalization factor and Rmult_le_pos to preserve nonnegativity.
   Library reuse: Stdlib.List.filter_In, Stdlib.Reals.Rinv_0_lt_compat/Rmult_le_pos and the existing conditioned_weights definition.
   Boundary: Nonnegative finite list masses are not a statement about unenumerated outcomes or continuous measures; the selection predicate is the exact supplied Boolean event.
 *)
Theorem conditioned_weights_nonnegative_on_filtered_samples :
  forall (A : Type) (samples : list A)
         (weight : A -> R) (given : A -> bool),
    0 < @FiniteUnion.finite_prob A weight samples given ->
    (forall x, In x samples -> 0 <= weight x) ->
    forall x, In x (filter given samples) ->
      0 <= conditioned_weights A weight samples given x.
Proof.
  intros A samples weight given Hpositive Hw x Hx.
  unfold conditioned_weights.
  apply Rmult_le_pos.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hpositive.
  - apply Hw.
    apply filter_In in Hx.
    tauto.
Qed.

(**
   [finite_conditional_independence_iff_conditioned_indicator_covariance_zero] (theorem) — Generic Boolean conditional independence as zero covariance under the normalized conditional sample.
   Mathematical meaning: For any strictly positive-mass conditioning event G, finite conditional independence of Boolean events A and B under G is equivalent to zero covariance of their indicator scores when computed over the G-filtered sample with weights normalized by P(G). This extends the earlier true-conditioning covariance bridge to arbitrary positive-mass finite Boolean selectors.
   Exact checked proposition: If 0 < finite_prob weight samples given, finite_conditional_independent weight samples first second given iff FiniteMoments.covariance (filter given samples) (conditioned_weights A weight samples given) (indicator first) (indicator second) = 0.
   Premises and side conditions: Strictly positive original conditioning mass is required for the normalization. The real-algebra equivalence does not need individual nonnegative weights; to interpret covariance and independence statistically the original sample must have nonnegative weights, established as preserved by the separate nonnegativity theorem. No full-sample unit normalization is needed.
   Proof/definition method: Rewrite original conditioning as true-event conditioning on the existing filtered sample; use the positive global scaling invariance of finite conditional independence to replace retained weights with normalized ones, and then instantiate the previously checked normalized indicator covariance/independence equivalence using conditioned_weights_total_mass_one.
   Library reuse: FiniteUnion.finite_conditional_independent_iff_filtered_true, FiniteUnion.finite_conditional_independent_scale_weights, finite_normalized_conditional_independence_iff_zero_indicator_covariance, conditioned_weights_total_mass_one and Stdlib.Reals.Rinv_0_lt_compat. No independent covariance calculation, finite sum or conditioning definition is introduced.
   Boundary: This is a discrete finite Boolean-indicator result under one conditioning selector, not an equivalence for arbitrary real-valued scores or continuous conditional covariance operators.
 *)
Theorem finite_conditional_independence_iff_conditioned_indicator_covariance_zero :
  forall (A : Type) (samples : list A)
         (weight : A -> R) (first second given : A -> bool),
    0 < @FiniteUnion.finite_prob A weight samples given ->
    (@FiniteUnion.finite_conditional_independent A
       weight samples first second given <->
     @FiniteMoments.covariance A (filter given samples)
       (conditioned_weights A weight samples given)
       (fun x => FiniteUnion.indicator (first x))
       (fun x => FiniteUnion.indicator (second x)) = 0).
Proof.
  intros A samples weight first second given Hpositive.
  rewrite (@FiniteUnion.finite_conditional_independent_iff_filtered_true
    A weight samples first second given).
  assert (Hscale :
      0 < / (@FiniteUnion.finite_prob A weight samples given)).
  { apply Rinv_0_lt_compat; exact Hpositive. }
  rewrite <- (@FiniteUnion.finite_conditional_independent_scale_weights
    A (/ (@FiniteUnion.finite_prob A weight samples given))
    weight (filter given samples) first second
    (fun _ => true) Hscale).
  unfold conditioned_weights.
  apply finite_normalized_conditional_independence_iff_zero_indicator_covariance.
  apply conditioned_weights_total_mass_one.
  exact Hpositive.
Qed.
