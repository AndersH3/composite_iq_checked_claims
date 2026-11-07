(* Bridge between the finite-event model and the finite-moment model.
   Both are interpreted with the shared Stdlib.List-based finite sum.
   The bridge does not assume independence, a measure axiom, or normality. *)
From Stdlib Require Import Reals Lra Psatz List Bool.
Require Import FiniteSum FiniteUnion FiniteMoments.
Import ListNotations.
Open Scope R_scope.

Theorem finite_sum_models_agree :
  forall (A : Type) (samples : list A) (f : A -> R),
    @FiniteUnion.finite_sum A f samples =
      @FiniteMoments.sum_finite A f samples.
Proof.
  reflexivity.
Qed.

Theorem finite_total_mass_models_agree :
  forall (A : Type) (samples : list A) (weight : A -> R),
    @FiniteMoments.total_mass A samples weight =
      @FiniteUnion.finite_sum A weight samples.
Proof.
  reflexivity.
Qed.

Theorem finite_event_probability_is_indicator_expectation :
  forall (A : Type) (samples : list A) (weight : A -> R)
         (event : A -> bool),
    @FiniteUnion.finite_prob A weight samples event =
      @FiniteMoments.expect A samples weight
        (fun x => FiniteUnion.indicator (event x)).
Proof.
  reflexivity.
Qed.

Lemma indicator_square :
  forall b,
    FiniteUnion.indicator b * FiniteUnion.indicator b =
      FiniteUnion.indicator b.
Proof.
  intros []; unfold FiniteUnion.indicator; ring.
Qed.

Lemma indicator_product_and :
  forall b c,
    FiniteUnion.indicator b * FiniteUnion.indicator c =
      FiniteUnion.indicator (andb b c).
Proof.
  intros [] []; unfold FiniteUnion.indicator; simpl; ring.
Qed.

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
