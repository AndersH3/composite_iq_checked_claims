(** Module: FiniteBridge.v
   Purpose: Checked interpretation between Boolean event mass and finite moments.
   Connects FiniteUnion event indicators to FiniteMoments expectation, variance, covariance and algebraic independence conditions.
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
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem
   finite_event_probability_is_indicator_expectation : forall (A : Type) (samples :
   list A) (weight : A -> R) (event : A -> bool), @FiniteUnion.finite_prob A weight
   samples event = @FiniteMoments.expect A samples weight (fun x =>
   FiniteUnion.indicator (event x)).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses definitional reduction.
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
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
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem finite_event_indicator_covariance : forall (A :
   Type) (samples : list A) (weight : A -> R) (a b : A -> bool),
   @FiniteMoments.covariance A samples weight (fun x => FiniteUnion.indicator (a x))
   (fun x => FiniteUnion.indicator (b x)) = @FiniteUnion.finite_prob A weight samples
   (fun x => andb (a x) (b x)) - @FiniteUnion.finite_prob A weight samples a *
   @FiniteUnion.finite_prob A weight samples b.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, definitional reduction; references include
   FiniteMoments.covariance., FiniteMoments.expectation_ext., indicator_product_and..
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
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
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   finite_event_independence_iff_zero_indicator_covariance : forall (A : Type)
   (samples : list A) (weight : A -> R) (a b : A -> bool), @FiniteMoments.covariance
   A samples weight (fun x => FiniteUnion.indicator (a x)) (fun x =>
   FiniteUnion.indicator (b x)) = 0 <-> @FiniteUnion.finite_prob A weight samples
   (fun x => andb (a x) (b x)) = @FiniteUnion.finite_prob A weight samples a *
   @FiniteUnion.finite_prob A weight samples b.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, linear real
   arithmetic (Lra); references include finite_event_indicator_covariance..
   Library reuse: FiniteUnion, FiniteMoments, FiniteSum and Stdlib.Bool/Reals.
   Boundary: Boolean event indicator algebra in an explicit finite sample, with
   normalized nonnegative weights when interpreting real expressions as
   probabilities.
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
