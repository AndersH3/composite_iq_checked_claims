(* Exact finite-sample moments for the Hoeflin/Ferguson report.
   Nonnegative normalized weights form an explicit finite probability model.
   All moment laws are derived from finite sums, not assumed as axioms.
   No Gaussian or empirical psychometric assumptions are used. *)
From Stdlib Require Import Reals Lra Psatz List.
Import ListNotations.
Open Scope R_scope.

Section FiniteProbabilityMoments.
  Variable Outcome : Type.
  Variable samples : list Outcome.
  Variable weight : Outcome -> R.

  Fixpoint sum_finite (f : Outcome -> R) (xs : list Outcome) : R :=
    match xs with
    | [] => 0
    | x :: rest => f x + sum_finite f rest
    end.

  Definition total_mass : R := sum_finite weight samples.

  Definition expect (f : Outcome -> R) : R :=
    sum_finite (fun x => weight x * f x) samples.

  Definition covariance (f g : Outcome -> R) : R :=
    expect (fun x => f x * g x) - expect f * expect g.

  Definition variance (f : Outcome -> R) : R := covariance f f.

  Definition centered_second_moment (f : Outcome -> R) : R :=
    expect (fun x => (f x - expect f) * (f x - expect f)).

  Lemma sum_finite_ext :
    forall xs f g,
      (forall x, f x = g x) ->
      sum_finite f xs = sum_finite g xs.
  Proof.
    induction xs as [|x xs IH]; intros f g Hfg; simpl.
    - reflexivity.
    - rewrite (Hfg x), (IH f g Hfg); reflexivity.
  Qed.

  Lemma sum_finite_add :
    forall xs f g,
      sum_finite (fun x => f x + g x) xs =
        sum_finite f xs + sum_finite g xs.
  Proof.
    induction xs as [|x xs IH]; intros f g; simpl.
    - ring.
    - rewrite IH; ring.
  Qed.

  Lemma sum_finite_scale :
    forall xs a f,
      sum_finite (fun x => a * f x) xs =
        a * sum_finite f xs.
  Proof.
    induction xs as [|x xs IH]; intros a f; simpl.
    - ring.
    - rewrite IH; ring.
  Qed.

  Lemma sum_finite_nonnegative :
    forall xs f,
      (forall x, In x xs -> 0 <= f x) ->
      0 <= sum_finite f xs.
  Proof.
    induction xs as [|x xs IH]; intros f Hf; simpl.
    - lra.
    - assert (Hx : 0 <= f x) by (apply Hf; simpl; auto).
      assert (Htail : forall y, In y xs -> 0 <= f y).
      { intros y Hy; apply Hf; simpl; auto. }
      specialize (IH f Htail); lra.
  Qed.

  Theorem expectation_ext :
    forall f g, (forall x, f x = g x) -> expect f = expect g.
  Proof.
    intros f g Hfg.
    unfold expect.
    apply sum_finite_ext.
    intro x; rewrite Hfg; reflexivity.
  Qed.

  Theorem expectation_add :
    forall f g,
      expect (fun x => f x + g x) = expect f + expect g.
  Proof.
    intros f g.
    unfold expect.
    transitivity
      (sum_finite (fun x =>
        weight x * f x + weight x * g x) samples).
    - apply sum_finite_ext; intro x; ring.
    - apply sum_finite_add.
  Qed.

  Theorem expectation_scale :
    forall a f,
      expect (fun x => a * f x) = a * expect f.
  Proof.
    intros a f.
    unfold expect.
    transitivity (sum_finite (fun x =>
      a * (weight x * f x)) samples).
    - apply sum_finite_ext; intro x; ring.
    - apply sum_finite_scale.
  Qed.

  Theorem expectation_zero :
    expect (fun _ => 0) = 0.
  Proof.
    unfold expect.
    induction samples as [|x xs IH]; simpl.
    - reflexivity.
    - rewrite IH; ring.
  Qed.

  Theorem expectation_constant :
    forall c, expect (fun _ => c) = c * total_mass.
  Proof.
    intro c.
    unfold expect, total_mass.
    transitivity (sum_finite (fun x => c * weight x) samples).
    - apply sum_finite_ext; intro x; ring.
    - rewrite sum_finite_scale; reflexivity.
  Qed.

  Theorem expectation_constant_normalized :
    forall c, total_mass = 1 -> expect (fun _ => c) = c.
  Proof.
    intros c Hmass.
    rewrite expectation_constant, Hmass; ring.
  Qed.

  Theorem expectation_sub :
    forall f g,
      expect (fun x => f x - g x) = expect f - expect g.
  Proof.
    intros f g.
    transitivity (expect (fun x => f x + (-1) * g x)).
    - apply expectation_ext; intro x; ring.
    - rewrite expectation_add, expectation_scale; ring.
  Qed.

  Theorem expectation_affine :
    forall f a b,
      total_mass = 1 ->
      expect (fun x => a * f x + b) = a * expect f + b.
  Proof.
    intros f a b Hmass.
    rewrite expectation_add, expectation_scale,
      expectation_constant_normalized by exact Hmass.
    ring.
  Qed.

  Theorem expectation_nonnegative :
    forall f,
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 <= f x) ->
      0 <= expect f.
  Proof.
    intros f Hw Hf.
    unfold expect.
    apply sum_finite_nonnegative.
    intros x Hx.
    pose proof (Hw x Hx).
    pose proof (Hf x Hx).
    nra.
  Qed.

  Theorem covariance_symmetric :
    forall f g, covariance f g = covariance g f.
  Proof.
    intros f g.
    unfold covariance.
    assert (Hprod :
      expect (fun x => f x * g x) =
      expect (fun x => g x * f x)).
    { apply expectation_ext; intro x; ring. }
    rewrite Hprod; ring.
  Qed.

  Theorem covariance_scale_first :
    forall f g a,
      covariance (fun x => a * f x) g = a * covariance f g.
  Proof.
    intros f g a.
    unfold covariance.
    rewrite expectation_scale.
    transitivity
      (expect (fun x => a * (f x * g x)) -
       a * expect f * expect g).
    - apply Rminus_eq_compat_r.
      apply expectation_ext; intro x; ring.
    - rewrite expectation_scale; ring.
  Qed.

  Theorem covariance_add_first :
    forall f g h,
      covariance (fun x => f x + g x) h =
        covariance f h + covariance g h.
  Proof.
    intros f g h.
    unfold covariance.
    rewrite expectation_add.
    replace (expect (fun x => (f x + g x) * h x))
      with (expect (fun x => f x * h x) +
            expect (fun x => g x * h x)).
    - ring.
    - transitivity
        (expect (fun x => f x * h x + g x * h x)).
      + apply expectation_ext; intro x; ring.
      + apply expectation_add.
  Qed.

  Theorem covariance_scale_second :
    forall f g a,
      covariance f (fun x => a * g x) = a * covariance f g.
  Proof.
    intros f g a.
    rewrite covariance_symmetric.
    rewrite covariance_scale_first.
    rewrite covariance_symmetric.
    reflexivity.
  Qed.

  Theorem covariance_add_second :
    forall f g h,
      covariance f (fun x => g x + h x) =
        covariance f g + covariance f h.
  Proof.
    intros f g h.
    rewrite covariance_symmetric.
    rewrite covariance_add_first.
    rewrite (covariance_symmetric g f).
    rewrite (covariance_symmetric h f).
    reflexivity.
  Qed.

  Theorem variance_second_moment :
    forall f,
      variance f = expect (fun x => f x * f x) -
                   expect f * expect f.
  Proof.
    intro f; reflexivity.
  Qed.

  Theorem variance_of_scaled_score :
    forall f a,
      variance (fun x => a * f x) = (a * a) * variance f.
  Proof.
    intros f a.
    unfold variance.
    rewrite covariance_scale_first, covariance_scale_second.
    ring.
  Qed.

  Theorem variance_of_two_score_sum :
    forall f g,
      variance (fun x => f x + g x) =
      variance f + variance g + 2 * covariance f g.
  Proof.
    intros f g.
    unfold variance.
    rewrite covariance_add_first.
    rewrite covariance_add_second.
    rewrite (covariance_add_second g f g).
    rewrite (covariance_symmetric g f).
    ring.
  Qed.

  Theorem centered_second_moment_identity :
    forall f,
      total_mass = 1 ->
      centered_second_moment f = variance f.
  Proof.
    intros f Hmass.
    unfold centered_second_moment.
    transitivity
      (expect (fun x =>
        f x * f x + ((-2 * expect f) * f x +
                          expect f * expect f))).
    - apply expectation_ext; intro x; ring.
    - rewrite expectation_add, expectation_add.
      rewrite expectation_scale.
      rewrite expectation_constant, Hmass.
      unfold variance, covariance; ring.
  Qed.

  Theorem variance_nonnegative :
    forall f,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <= variance f.
  Proof.
    intros f Hmass Hw.
    rewrite <- (centered_second_moment_identity f Hmass).
    unfold centered_second_moment.
    apply expectation_nonnegative.
    - exact Hw.
    - intros x Hx; nra.
  Qed.

  Theorem covariance_with_constant_first :
    forall f c, total_mass = 1 ->
      covariance (fun _ => c) f = 0.
  Proof.
    intros f c Hmass.
    unfold covariance.
    rewrite (expectation_constant_normalized c Hmass).
    transitivity
      (expect (fun x => c * f x) - c * expect f).
    - reflexivity.
    - rewrite expectation_scale; ring.
  Qed.

  Theorem variance_of_shifted_score :
    forall f c, total_mass = 1 ->
      variance (fun x => f x + c) = variance f.
  Proof.
    intros f c Hmass.
    unfold variance.
    rewrite covariance_add_first.
    rewrite covariance_add_second.
    rewrite covariance_add_second.
    assert (Hc1 : covariance (fun _ => c) f = 0)
      by (apply covariance_with_constant_first; exact Hmass).
    assert (Hc2 : covariance f (fun _ => c) = 0).
    { rewrite covariance_symmetric; exact Hc1. }
    assert (Hcc : covariance (fun _ => c) (fun _ => c) = 0).
    { apply covariance_with_constant_first; exact Hmass. }
    rewrite Hc1, Hc2, Hcc; ring.
  Qed.

End FiniteProbabilityMoments.
