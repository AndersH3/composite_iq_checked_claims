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
   [finite_sum_models_agree] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: R), @FiniteUnion.finite_sum A f samples =
   @FiniteMoments.sum_finite A f samples.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: definitional computation.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
 *)
Theorem finite_sum_models_agree :
  forall (A : Type) (samples : list A) (f : A -> R),
    @FiniteUnion.finite_sum A f samples =
      @FiniteMoments.sum_finite A f samples.
Proof.
  reflexivity.
Qed.

(**
   [finite_total_mass_models_agree] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: R), @FiniteMoments.total_mass A samples weight =
   @FiniteUnion.finite_sum A weight samples.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: definitional computation.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
 *)
Theorem finite_total_mass_models_agree :
  forall (A : Type) (samples : list A) (weight : A -> R),
    @FiniteMoments.total_mass A samples weight =
      @FiniteUnion.finite_sum A weight samples.
Proof.
  reflexivity.
Qed.

(**
   [finite_event_probability_is_indicator_expectation] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: bool), @FiniteUnion.finite_prob A weight samples event =
   @FiniteMoments.expect A samples weight (fun x => FiniteUnion.indicator
   (event x)).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: definitional computation.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [indicator_square] (lemma).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: forall b, FiniteUnion.indicator b * FiniteUnion.indicator
   b = FiniteUnion.indicator b.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably FiniteUnion.indicator.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
 *)
Lemma indicator_square :
  forall b,
    FiniteUnion.indicator b * FiniteUnion.indicator b =
      FiniteUnion.indicator b.
Proof.
  intros []; unfold FiniteUnion.indicator; ring.
Qed.

(**
   [indicator_product_and] (lemma).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: forall b c, FiniteUnion.indicator b *
   FiniteUnion.indicator c = FiniteUnion.indicator (andb b c).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: ring/field normalization; notably FiniteUnion.indicator.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
 *)
Lemma indicator_product_and :
  forall b c,
    FiniteUnion.indicator b * FiniteUnion.indicator c =
      FiniteUnion.indicator (andb b c).
Proof.
  intros [] []; unfold FiniteUnion.indicator; simpl; ring.
Qed.

(**
   [finite_event_indicator_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: bool), @FiniteMoments.variance A samples weight (fun x =>
   FiniteUnion.indicator (event x)) = @FiniteUnion.finite_prob A weight samples
   event * (1 - @FiniteUnion.finite_prob A weight samples event).
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably FiniteMoments.expectation_ext.,
   indicator_square., Hsquare..
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_indicator_covariance] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: bool), @FiniteMoments.covariance A samples weight (fun x
   => FiniteUnion.indicator (a x)) (fun x => FiniteUnion.indicator (b x)) =
   @FiniteUnion.finite_prob A weight samples (fun x => andb (a x) (b x)) -
   @FiniteUnion.finite_prob A weight samples a * @FiniteUnion.finite_prob A
   weight samples b.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably FiniteMoments.covariance.,
   FiniteMoments.expectation_ext., indicator_product_and..
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_independence_iff_zero_indicator_covariance] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: bool), @FiniteMoments.covariance A samples weight (fun x
   => FiniteUnion.indicator (a x)) (fun x => FiniteUnion.indicator (b x)) = 0
   <-> @FiniteUnion.finite_prob A weight samples (fun x => andb (a x) (b x)) =
   @FiniteUnion.finite_prob A weight samples a * @FiniteUnion.finite_prob A
   weight samples b.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic; notably
   finite_event_indicator_covariance..
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_indicator_zero_variance_iff_extreme_mass] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: bool), @FiniteMoments.variance A samples weight (fun x =>
   FiniteUnion.indicator (event x)) = 0 <-> @FiniteUnion.finite_prob A weight
   samples event = 0 \/ @FiniteUnion.finite_prob A weight samples event = 1.
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, Stdlib Lra linear arithmetic, ring/field
   normalization; notably finite_event_indicator_variance., Rmult_integral.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_indicator_variance_at_most_quarter] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: bool), @FiniteMoments.variance A samples weight (fun x =>
   FiniteUnion.indicator (event x)) <= /4.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Psatz nonlinear arithmetic; notably finite_event_indicator_variance.,
   Rle_0_sqr..
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_indicator_complement_variance] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: @FiniteMoments.variance A samples weight (fun x =>
   FiniteUnion.indicator (negb (event x))) = @FiniteMoments.variance A samples
   weight (fun x => FiniteUnion.indicator (event x)).
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_indicator_covariance_complement_second] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: @FiniteMoments.covariance A samples weight (fun x =>
   FiniteUnion.indicator (a x)) (fun x => FiniteUnion.indicator (negb (b x))) =
   - @FiniteMoments.covariance A samples weight (fun x => FiniteUnion.indicator
   (a x)) (fun x => FiniteUnion.indicator (b x)).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, ring/field normalization, definitional computation;
   notably FiniteMoments.covariance_extensional..
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_indicator_covariance_complement_first] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: @FiniteMoments.covariance A samples weight (fun x =>
   FiniteUnion.indicator (negb (a x))) (fun x => FiniteUnion.indicator (b x)) =
   - @FiniteMoments.covariance A samples weight (fun x => FiniteUnion.indicator
   (a x)) (fun x => FiniteUnion.indicator (b x)).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably finite_event_indicator_covariance_complement_second..
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
   [finite_event_indicator_covariance_complement_both] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: @FiniteMoments.covariance A samples weight (fun x =>
   FiniteUnion.indicator (negb (a x))) (fun x => FiniteUnion.indicator (negb (b
   x))) = @FiniteMoments.covariance A samples weight (fun x =>
   FiniteUnion.indicator (a x)) (fun x => FiniteUnion.indicator (b x)).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   finite_event_indicator_covariance_complement_first,
   finite_event_indicator_covariance_complement_second.
   Library discipline: FiniteSum, FiniteUnion, FiniteMoments and Rocq's
   Bool/Reals tactics.
   Scope: Zero indicator covariance corresponds to a finite event product
   identity, not statistical independence for arbitrary continuous
   distributions.
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
