(** Module: FiniteMoments.v
   Purpose: Finite weighted expectations, covariance algebra and score matrices.
   Derives moment linearity, variance bounds, composite-score covariance, and finite-list covariance-matrix formulas from a common finite sum.
   Mathematical representation: A fixed list of samples and a real weight function define expectation; covariance and variance are differences/products of expectations.
   Explicit hypotheses: Where a claim needs genuine probability, hypotheses require normalized total mass and nonnegative weights; vector identities require compatible list lengths.
   Library use: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's reusable fold, extensionality, monotonicity and Fubini lemmas.
   Limitations: No assertion about Gaussian covariance, continuous random variables or observed IQ distributions follows from this finite model.
   Proof documentation: Every public and helper declaration below has its
   own statement, hypothesis, proof-approach, and scope commentary.
   Reproduction: rocq compile FiniteMoments.v (after imported local modules);
   see rocq/README.md and rocq/LIBRARY_AUDIT.md for dependency order,
   checked-claim mapping, and library audit. All results are Rocq-kernel
   checked; no unchecked evidence is created by comments.
 *)
(* Exact finite-sample moments for the Hoeflin/Ferguson report.
   Nonnegative normalized weights form an explicit finite probability model.
   All moment laws are derived from finite sums, not assumed as axioms.
   No Gaussian or empirical psychometric assumptions are used. *)
From Stdlib Require Import Reals Lra Psatz List Sorting.Permutation.
Require Import FiniteSum.
Import ListNotations.
Open Scope R_scope.

Section FiniteProbabilityMoments.
  Variable Outcome : Type.
  Variable samples : list Outcome.
  Variable weight : Outcome -> R.

  (* Keep the original public name as a transparent alias.  Both this
     moment model and FiniteUnion now use the same shared Stdlib fold. *)
  (**
   [sum_finite] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: The outcome-specialized alias of the generic
   finite real list sum, summing an integrand once per listed
   outcome occurrence with no deduplication.
   Exact declaration: Definition sum_finite (f : Outcome -> R) (xs : list Outcome) :
   R := FiniteSum.finite_sum f xs.
   Premises and side conditions: The list is finite and its integrand may be signed.
   Normalization and probability semantics are not assumed.
   Proof/definition method: Uses FiniteSum.finite_sum directly,
   reusing the checked shared fold, extensionality, arithmetic
   and permutation results instead of implementing another sum.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition sum_finite (f : Outcome -> R) (xs : list Outcome) : R :=
    FiniteSum.finite_sum f xs.

  (**
   [total_mass] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Sums the sample weight assigned to every
   listed outcome occurrence. This number is the normalizing
   mass for the module's finite weighted moment functional.
   Exact declaration: Definition total_mass : R := sum_finite weight samples.
   Premises and side conditions: The weights need not be positive or normalized
   in this definition. Theorems interpreting the functional
   as probability require total_mass = 1 and nonnegative weights.
   Proof/definition method: Delegates to sum_finite weight samples,
   thereby inheriting exactly the same list-fold semantics,
   including repeated outcome occurrences.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition total_mass : R := sum_finite weight samples.

  (**
   [expect] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Applies the weighted linear functional
   E[f] = sum over sample occurrences of weight(x)*f(x).
   It is a true finite expected value when weights define a
   nonnegative normalized mass on those occurrences.
   Exact declaration: Definition expect (f : Outcome -> R) : R := sum_finite (fun x
   => weight x * f x) samples.
   Premises and side conditions: Arbitrary real-valued scores and sample weights
   are supported algebraically. Division by total_mass is not
   performed; any normalization assumption is stated by the theorem.
   Proof/definition method: Uses the shared sum_finite over the
   pointwise product of weight and score; linearity follows
   from the generic finite-sum addition and scaling laws.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition expect (f : Outcome -> R) : R :=
    sum_finite (fun x => weight x * f x) samples.

  (**
   [covariance] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Defines the finite algebraic bilinear expression
   E[f*g] - E[f]*E[g]. With nonnegative normalized sample weights
   this is the standard covariance of real score functions.
   Exact declaration: Definition covariance (f g : Outcome -> R) : R := expect (fun x
   => f x * g x) - expect f * expect g.
   Premises and side conditions: For unnormalized or signed sample weights, the
   expression is still well-defined, but standard positivity
   or constant-shift covariance facts may require total_mass=1.
   Proof/definition method: Uses the already defined expect twice
   and Stdlib.Reals multiplication/subtraction; subsequent
   bilinearity and symmetry are checked as separate theorems.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition covariance (f g : Outcome -> R) : R :=
    expect (fun x => f x * g x) - expect f * expect g.

  (**
   [variance] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Defines the variance expression as self-covariance
   Cov(f,f) rather than maintaining a second sum implementation.
   For nonnegative weights and unit total mass it equals the
   usual nonnegative centered second moment.
   Exact declaration: Definition variance (f : Outcome -> R) : R := covariance f f.
   Premises and side conditions: No assumptions are built into the definition.
   The proof of nonnegativity and its centered-moment
   interpretation explicitly requires suitable weight hypotheses.
   Proof/definition method: Reuses covariance f f by definition,
   so all covariance identities and the generic finite-sum
   algebra apply without a competing variance implementation.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition variance (f : Outcome -> R) : R := covariance f f.

  (**
   [centered_second_moment] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Computes E[(f-E[f])*(f-E[f])]
   using the current weighted mean. When total_mass=1, it is
   algebraically identical to variance f.
   Exact declaration: Definition centered_second_moment (f : Outcome -> R) : R :=
   expect (fun x => (f x - expect f) * (f x - expect f)).
   Premises and side conditions: This is a finite real-weighted expression.
   Without unit mass the centered identity differs from
   self-covariance; with signed weights it need not be nonnegative.
   Proof/definition method: Uses the same expect function and
   pointwise real subtraction/multiplication; the equality to
   variance is established separately with explicit normalization.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition centered_second_moment (f : Outcome -> R) : R :=
    expect (fun x => (f x - expect f) * (f x - expect f)).

  (**
   [sum_finite_ext] (lemma) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma sum_finite_ext : forall xs f g, (forall x, f x =
   g x) -> sum_finite f xs = sum_finite g xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma sum_finite_ext :
    forall xs f g,
      (forall x, f x = g x) ->
      sum_finite f xs = sum_finite g xs.
  Proof.
    intros xs f g Hfg.
    apply FiniteSum.finite_sum_ext; exact Hfg.
  Qed.

  (**
   [sum_finite_add] (lemma) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma sum_finite_add : forall xs f g, sum_finite (fun x
   => f x + g x) xs = sum_finite f xs + sum_finite g xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_add..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma sum_finite_add :
    forall xs f g,
      sum_finite (fun x => f x + g x) xs =
        sum_finite f xs + sum_finite g xs.
  Proof.
    intros xs f g.
    apply FiniteSum.finite_sum_add.
  Qed.

  (**
   [sum_finite_scale] (lemma) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma sum_finite_scale : forall xs a f, sum_finite (fun
   x => a * f x) xs = a * sum_finite f xs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_scale..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma sum_finite_scale :
    forall xs a f,
      sum_finite (fun x => a * f x) xs =
        a * sum_finite f xs.
  Proof.
    intros xs a f.
    apply FiniteSum.finite_sum_scale.
  Qed.

  (**
   [sum_finite_nonnegative] (lemma) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma sum_finite_nonnegative : forall xs f, (forall x,
   In x xs -> 0 <= f x) -> 0 <= sum_finite f xs.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions; sample or list membership. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_nonnegative.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma sum_finite_nonnegative :
    forall xs f,
      (forall x, In x xs -> 0 <= f x) ->
      0 <= sum_finite f xs.
  Proof.
    intros xs f Hf.
    apply FiniteSum.finite_sum_nonnegative; exact Hf.
  Qed.

  (**
   [expectation_extensional_on_samples] (theorem) — Enumerated support extensionality of finite moments.
   Mathematical meaning: Two scores that agree at every enumerated outcome have exactly equal weighted finite expectations, regardless of their values on outcomes outside the sample.
   Exact checked proposition: For all f g, equality at every x with In x samples implies expect f = expect g.
   Premises and side conditions: No weight normalization, sign restrictions, independence, or distinctness of enumerated outcomes is assumed. Each sample occurrence retains its original multiplicity.
   Proof/definition method: Unfold the project aliases for expectation and finite summation, then directly apply FiniteSum.finite_sum_ext_in to the weighted score integrands; rewrite the pointwise agreement at each listed outcome.
   Library reuse: FiniteSum.finite_sum_ext_in, Stdlib.List.map_ext_in and Stdlib.List.In.
   Boundary: The result is extensionality for an explicit finite list, not an almost-everywhere result for a general measure.
   *)
  Theorem expectation_extensional_on_samples :
    forall f g,
      (forall x, In x samples -> f x = g x) ->
      expect f = expect g.
  Proof.
    intros f g Hfg.
    unfold expect, sum_finite.
    apply FiniteSum.finite_sum_ext_in.
    intros x Hx.
    rewrite (Hfg x Hx).
    reflexivity.
  Qed.

  (**
   [expectation_ext] (theorem) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_ext : forall f g, (forall x, f x =
   g x) -> expect f = expect g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Apply the stronger expectation_extensional_on_samples theorem, since equality on all outcomes entails equality on the enumerated sample.
   Library reuse: expectation_extensional_on_samples, FiniteSum.finite_sum_ext_in and Stdlib.List.In.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem expectation_ext :
    forall f g, (forall x, f x = g x) -> expect f = expect g.
  Proof.
    intros f g Hfg.
    apply expectation_extensional_on_samples.
    intros x _; apply Hfg.
  Qed.

  (**
   [expectation_add] (theorem) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_add : forall f g, expect (fun x =>
   f x + g x) = expect f + expect g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   expect., sum_finite_ext, sum_finite_add..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [expectation_scale] (theorem) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_scale : forall a f, expect (fun x
   => a * f x) = a * expect f.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   expect., sum_finite_ext, sum_finite_scale..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [expectation_zero] (theorem) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_zero : expect (fun _ => 0) = 0.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   expect., sum_finite_ext, FiniteSum.finite_sum_zero..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem expectation_zero :
    expect (fun _ => 0) = 0.
  Proof.
    unfold expect.
    transitivity (sum_finite (fun _ => 0) samples).
    - apply sum_finite_ext; intro x; ring.
    - apply FiniteSum.finite_sum_zero.
  Qed.

  (**
   [expectation_constant] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_constant : forall c, expect (fun _
   => c) = c * total_mass.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization, definitional reduction;
   references include expect, sum_finite_ext, sum_finite_scale.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem expectation_constant :
    forall c, expect (fun _ => c) = c * total_mass.
  Proof.
    intro c.
    unfold expect, total_mass.
    transitivity (sum_finite (fun x => c * weight x) samples).
    - apply sum_finite_ext; intro x; ring.
    - rewrite sum_finite_scale; reflexivity.
  Qed.

  (**
   [expectation_constant_normalized] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_constant_normalized : forall c,
   total_mass = 1 -> expect (fun _ => c) = c.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include expectation_constant.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem expectation_constant_normalized :
    forall c, total_mass = 1 -> expect (fun _ => c) = c.
  Proof.
    intros c Hmass.
    rewrite expectation_constant, Hmass; ring.
  Qed.

  (**
   [expectation_sub] (theorem) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_sub : forall f g, expect (fun x =>
   f x - g x) = expect f - expect g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   expect, FiniteSum.finite_sum_ext, FiniteSum.finite_sum_sub..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem expectation_sub :
    forall f g,
      expect (fun x => f x - g x) = expect f - expect g.
  Proof.
    intros f g.
    unfold expect, sum_finite.
    transitivity (FiniteSum.finite_sum
      (fun x => weight x * f x - weight x * g x) samples).
    - apply FiniteSum.finite_sum_ext; intro x; ring.
    - apply FiniteSum.finite_sum_sub.
  Qed.

  (**
   [expectation_affine] (theorem) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_affine : forall f a b, total_mass =
   1 -> expect (fun x => a * f x + b) = a * expect f + b.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   expectation_add, Hmass..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [expectation_nonnegative] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem expectation_nonnegative : forall f, (forall x,
   In x samples -> 0 <= weight x) -> (forall x, In x samples -> 0 <= f x) -> 0 <=
   expect f.
   Premises and side conditions: The displayed hypotheses include nonnegative outcome
   weights; explicit nonzero or strict-positive numerical conditions; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas,
   polynomial real arithmetic (Psatz); references include expect.,
   sum_finite_nonnegative..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [covariance_symmetric] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_symmetric : forall f g, covariance f
   g = covariance g f.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   covariance., expectation_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [covariance_scale_first] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_scale_first : forall f g a,
   covariance (fun x => a * f x) g = a * covariance f g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   covariance., expectation_scale., Rminus_eq_compat_r..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [covariance_add_first] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_add_first : forall f g h, covariance
   (fun x => f x + g x) h = covariance f h + covariance g h.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   covariance., expectation_add., expectation_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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
      + symmetry; apply expectation_add.
      + apply expectation_ext; intro x; ring.
  Qed.

  (**
   [covariance_scale_second] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_scale_second : forall f g a,
   covariance f (fun x => a * g x) = a * covariance f g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include covariance_symmetric., covariance_scale_first..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [covariance_add_second] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_add_second : forall f g h,
   covariance f (fun x => g x + h x) = covariance f g + covariance f h.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include covariance_symmetric., covariance_add_first.,
   covariance_symmetric.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [variance_second_moment] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_second_moment : forall f, variance f =
   expect (fun x => f x * f x) - expect f * expect f.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses definitional reduction.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_second_moment :
    forall f,
      variance f = expect (fun x => f x * f x) -
                   expect f * expect f.
  Proof.
    intro f; reflexivity.
  Qed.

  (**
   [variance_of_scaled_score] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_scaled_score : forall f a, variance
   (fun x => a * f x) = (a * a) * variance f.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include variance., covariance_scale_first.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_scaled_score :
    forall f a,
      variance (fun x => a * f x) = (a * a) * variance f.
  Proof.
    intros f a.
    unfold variance.
    rewrite covariance_scale_first, covariance_scale_second.
    ring.
  Qed.

  (**
   [variance_of_two_score_sum] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_two_score_sum : forall f g,
   variance (fun x => f x + g x) = variance f + variance g + 2 * covariance f g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include variance., covariance_add_first.,
   covariance_add_second..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [centered_second_moment_identity] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Expresses a checked identity or bound within the finite
   weighted score expectations, variances and covariance matrices.
   Exact checked proposition: Theorem centered_second_moment_identity : forall f,
   total_mass = 1 -> centered_second_moment f = variance f.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   centered_second_moment., expectation_ext, expectation_add.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [variance_nonnegative] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_nonnegative : forall f, total_mass = 1
   -> (forall x, In x samples -> 0 <= weight x) -> 0 <= variance f.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include centered_second_moment.,
   expectation_nonnegative., Rle_0_sqr..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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
    - intros x Hx.
      change (0 <= Rsqr (f x - expect f)).
      apply Rle_0_sqr.
  Qed.

  (**
   [covariance_with_constant_first] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_with_constant_first : forall f c,
   total_mass = 1 -> covariance (fun _ => c) f = 0.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization, definitional reduction; references include covariance.,
   expectation_constant_normalized, expectation_scale.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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

  (**
   [variance_of_shifted_score] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_shifted_score : forall f c,
   total_mass = 1 -> variance (fun x => f x + c) = variance f.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   variance., covariance_add_first., covariance_add_second..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
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


  (* Further elementary consequences for the report's weighted composites.
     These require only finite expectation algebra and, where noted,
     a normalized finite probability mass. *)

  (**
   [covariance_extensional_on_samples] (theorem) — Enumerated support extensionality of finite moments.
   Mathematical meaning: Covariance of finite real scores depends only on the values of both score functions at enumerated outcome occurrences; changes elsewhere do not affect the two marginals or their product expectation.
   Exact checked proposition: For all f f' g g', equalities f x = f' x and g x = g' x on every x in samples imply covariance f g = covariance f' g'.
   Premises and side conditions: The sample list and weights can be arbitrary, including repeated outcomes and signed weights. Equality is algebraic and does not assume independence, normalization or nonnegative variances.
   Proof/definition method: Unfold covariance into the expected product and product of expectations, reuse expectation_extensional_on_samples on all three terms, and conclude by rewriting the pointwise products.
   Library reuse: expectation_extensional_on_samples, FiniteSum.finite_sum_ext_in, Stdlib.List.In and real-number algebra.
   Boundary: Finite weighted-list semantics only; no claims about equality of continuous distributions or empirical covariance.
   *)
  Theorem covariance_extensional_on_samples :
    forall f f' g g',
      (forall x, In x samples -> f x = f' x) ->
      (forall x, In x samples -> g x = g' x) ->
      covariance f g = covariance f' g'.
  Proof.
    intros f f' g g' Hf Hg.
    unfold covariance.
    rewrite (expectation_extensional_on_samples f f' Hf).
    rewrite (expectation_extensional_on_samples g g' Hg).
    assert (Hprod :
      expect (fun x => f x * g x) =
      expect (fun x => f' x * g' x)).
    { apply expectation_extensional_on_samples.
      intros x Hx.
      rewrite (Hf x Hx), (Hg x Hx).
      reflexivity. }
    rewrite Hprod.
    reflexivity.
  Qed.

  (**
   [covariance_extensional] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_extensional : forall f f' g g',
   (forall x, f x = f' x) -> (forall x, g x = g' x) -> covariance f g = covariance f'
   g'.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Apply covariance_extensional_on_samples instead of duplicating three expectation and product rewrites.
   Library reuse: covariance_extensional_on_samples, expectation_extensional_on_samples and Stdlib.List.In.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_extensional :
    forall f f' g g',
      (forall x, f x = f' x) ->
      (forall x, g x = g' x) ->
      covariance f g = covariance f' g'.
  Proof.
    intros f f' g g' Hf Hg.
    apply covariance_extensional_on_samples.
    - intros x _; apply Hf.
    - intros x _; apply Hg.
  Qed.

  (**
   [variance_extensional_on_samples] (theorem) — Enumerated support extensionality of finite moments.
   Mathematical meaning: Finite variance is unchanged when one score function is replaced with another that agrees at every enumerated sample outcome, even if they disagree on unobserved outcomes.
   Exact checked proposition: For any f g, on-sample equality implies variance f = variance g.
   Premises and side conditions: There are no hypotheses about nonnegative weights, total mass, outcome uniqueness or the statistical relationship of the score functions; this is equality of finite algebraic variance expressions.
   Proof/definition method: Unfold variance as self-covariance and invoke the shared covariance_extensional_on_samples theorem with the same sampled equality on both arguments.
   Library reuse: covariance_extensional_on_samples, FiniteMoments.variance, Stdlib.List.In and FiniteSum.
   Boundary: This theorem does not assert variance positivity for signed or unnormalized weights and does not establish global functional equality.
   *)
  Theorem variance_extensional_on_samples :
    forall f g,
      (forall x, In x samples -> f x = g x) ->
      variance f = variance g.
  Proof.
    intros f g Hfg.
    unfold variance.
    apply covariance_extensional_on_samples; exact Hfg.
  Qed.

  (**
   [variance_extensional] (theorem) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_extensional : forall f g, (forall x, f
   x = g x) -> variance f = variance g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Delegate directly to variance_extensional_on_samples rather than unfold covariance again.
   Library reuse: variance_extensional_on_samples, covariance_extensional_on_samples and the shared FiniteSum model.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_extensional :
    forall f g, (forall x, f x = g x) ->
      variance f = variance g.
  Proof.
    intros f g Hfg.
    apply variance_extensional_on_samples.
    intros x _; apply Hfg.
  Qed.

  (**
   [centered_score_has_zero_expectation] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem centered_score_has_zero_expectation : forall f,
   total_mass = 1 -> expect (fun x => f x - expect f) = 0.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include expectation_sub.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem centered_score_has_zero_expectation :
    forall f, total_mass = 1 ->
      expect (fun x => f x - expect f) = 0.
  Proof.
    intros f Hmass.
    rewrite expectation_sub, expectation_constant, Hmass.
    ring.
  Qed.

  (**
   [covariance_with_constant_second] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_with_constant_second : forall f c,
   total_mass = 1 -> covariance f (fun _ => c) = 0.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include covariance_symmetric.,
   covariance_with_constant_first, Hmass..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_with_constant_second :
    forall f c, total_mass = 1 ->
      covariance f (fun _ => c) = 0.
  Proof.
    intros f c Hmass.
    rewrite covariance_symmetric.
    apply covariance_with_constant_first; exact Hmass.
  Qed.

  (**
   [covariance_invariant_under_first_shift] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_invariant_under_first_shift : forall
   f g c, total_mass = 1 -> covariance (fun x => f x + c) g = covariance f g.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include covariance_add_first.,
   covariance_with_constant_first.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_invariant_under_first_shift :
    forall f g c, total_mass = 1 ->
      covariance (fun x => f x + c) g = covariance f g.
  Proof.
    intros f g c Hmass.
    rewrite covariance_add_first.
    rewrite (covariance_with_constant_first g c Hmass).
    ring.
  Qed.

  (**
   [covariance_invariant_under_second_shift] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_invariant_under_second_shift :
   forall f g c, total_mass = 1 -> covariance f (fun x => g x + c) = covariance f g.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include covariance_add_second.,
   covariance_with_constant_second.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_invariant_under_second_shift :
    forall f g c, total_mass = 1 ->
      covariance f (fun x => g x + c) = covariance f g.
  Proof.
    intros f g c Hmass.
    rewrite covariance_add_second.
    rewrite (covariance_with_constant_second f c Hmass).
    ring.
  Qed.

  (**
   [variance_of_two_weighted_scores] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_two_weighted_scores : forall f g a
   b, variance (fun x => a * f x + b * g x) = (a * a) * variance f + (b * b) *
   variance g + 2 * a * b * covariance f g.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include variance_of_two_score_sum.,
   covariance_scale_first.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_two_weighted_scores :
    forall f g a b,
      variance (fun x => a * f x + b * g x) =
        (a * a) * variance f +
        (b * b) * variance g +
        2 * a * b * covariance f g.
  Proof.
    intros f g a b.
    rewrite variance_of_two_score_sum.
    rewrite !variance_of_scaled_score.
    rewrite covariance_scale_first, covariance_scale_second.
    ring.
  Qed.

  (**
   [covariance_of_two_weighted_pairs] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_of_two_weighted_pairs : forall f g h
   k a b c d, covariance (fun x => a * f x + b * g x) (fun x => c * h x + d * k x) =
   a * c * covariance f h + a * d * covariance f k + b * c * covariance g h + b * d *
   covariance g k.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include covariance_add_first., covariance_add_second.,
   covariance_add_second.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_of_two_weighted_pairs :
    forall f g h k a b c d,
      covariance (fun x => a * f x + b * g x)
                 (fun x => c * h x + d * k x) =
        a * c * covariance f h +
        a * d * covariance f k +
        b * c * covariance g h +
        b * d * covariance g k.
  Proof.
    intros f g h k a b c d.
    rewrite covariance_add_first.
    rewrite covariance_add_second.
    rewrite (covariance_add_second (fun x => b * g x)
                                  (fun x => c * h x)
                                  (fun x => d * k x)).
    repeat rewrite covariance_scale_first.
    repeat rewrite covariance_scale_second.
    ring.
  Qed.

  (**
   [variance_of_two_score_average] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_two_score_average : forall f g,
   variance (fun x => (f x + g x) / 2) = (variance f + variance g + 2 * covariance f
   g) / 4.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   variance_extensional, variance_of_scaled_score.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_two_score_average :
    forall f g,
      variance (fun x => (f x + g x) / 2) =
        (variance f + variance g + 2 * covariance f g) / 4.
  Proof.
    intros f g.
    transitivity
      (variance (fun x => (/2) * (f x + g x))).
    - apply variance_extensional; intro x.
      unfold Rdiv; ring.
    - rewrite variance_of_scaled_score, variance_of_two_score_sum.
      field.
  Qed.

  (**
   [variance_of_two_unit_variance_average] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_two_unit_variance_average : forall
   f g, variance f = 1 -> variance g = 1 -> variance (fun x => (f x + g x) / 2) = (1
   + covariance f g) / 2.
   Premises and side conditions: The displayed hypotheses include stated
   unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include variance_of_two_score_average..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_two_unit_variance_average :
    forall f g,
      variance f = 1 -> variance g = 1 ->
      variance (fun x => (f x + g x) / 2) =
        (1 + covariance f g) / 2.
  Proof.
    intros f g Hf Hg.
    rewrite variance_of_two_score_average.
    rewrite Hf, Hg; field.
  Qed.

  (**
   [variance_of_standardized_score] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_standardized_score : forall f mu
   sd, total_mass = 1 -> sd <> 0 -> sd * sd = variance f -> variance (fun x => (f x -
   mu) / sd) = 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; explicit nonzero or strict-positive numerical conditions; stated
   unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra), ring/field
   normalization; references include variance_extensional, variance_of_scaled_score.,
   variance_of_shifted_score.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_standardized_score :
    forall f mu sd,
      total_mass = 1 ->
      sd <> 0 ->
      sd * sd = variance f ->
      variance (fun x => (f x - mu) / sd) = 1.
  Proof.
    intros f mu sd Hmass Hsd Hvar.
    transitivity
      (variance (fun x => (/sd) * (f x + (-mu)))).
    - apply variance_extensional; intro x.
      unfold Rdiv; ring.
    - rewrite variance_of_scaled_score.
      rewrite (variance_of_shifted_score f (-mu) Hmass).
      rewrite <- Hvar.
      field; lra.
  Qed.

  (**
   [variance_of_iq_reporting_scale] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_iq_reporting_scale : forall f mu sd
   scale, total_mass = 1 -> sd <> 0 -> sd * sd = variance f -> variance (fun x => 100
   + scale * ((f x - mu) / sd)) = scale * scale.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; explicit nonzero or strict-positive numerical conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   variance_extensional, variance_of_shifted_score, variance_of_scaled_score..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_iq_reporting_scale :
    forall f mu sd scale,
      total_mass = 1 ->
      sd <> 0 ->
      sd * sd = variance f ->
      variance (fun x => 100 + scale * ((f x - mu) / sd)) =
        scale * scale.
  Proof.
    intros f mu sd scale Hmass Hsd Hvar.
    transitivity
      (variance (fun x => scale * ((f x - mu) / sd) + 100)).
    - apply variance_extensional; intro x; ring.
    - rewrite (variance_of_shifted_score
        (fun x => scale * ((f x - mu) / sd)) 100 Hmass).
      rewrite variance_of_scaled_score.
      rewrite (variance_of_standardized_score f mu sd Hmass Hsd Hvar).
      ring.
  Qed.


  (* General, arbitrary-length finite weighted composites.  The expression
     quadratic_form xs ys is the explicitly expanded sum of all
     a_i b_j Cov(X_i,Y_j); no matrix or covariance axioms are postulated. *)

  (* Weighted scores are a standard finite fold over (coefficient,score)
     pairs; no separate recursive evaluator is needed. *)
  (**
   [linear_combination] (definition) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Defines a finite composite score
   x -> sum_i a_i*g_i(x) from a list of real coefficients
   and outcome-to-real score functions, retaining duplicates.
   Exact declaration: Definition linear_combination (components : list (R * (Outcome
   -> R))) (x : Outcome) : R := FiniteSum.finite_sum (fun c => fst c * snd c x)
   components.
   Premises and side conditions: The real coefficients need not be positive,
   normalized or sum to one; they are score weights, distinct
   from the module's outcome probability weights.
   Proof/definition method: Uses FiniteSum.finite_sum over
   coefficient-score products with Stdlib pair projections;
   no custom recursive vector representation is introduced.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition linear_combination
    (components : list (R * (Outcome -> R))) (x : Outcome) : R :=
    FiniteSum.finite_sum (fun c => fst c * snd c x) components.

  (* Apply the built-in list fold to weighted component expectations. *)
  (**
   [linear_expectation] (definition) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Computes the coefficient-weighted sum of the
   expectations of each component score. The checked linearity
   theorem equates this expression with the expectation of
   the corresponding linear_combination.
   Exact declaration: Definition linear_expectation (components : list (R * (Outcome
   -> R))) : R := FiniteSum.finite_sum (fun c => fst c * expect (snd c)) components.
   Premises and side conditions: Coefficients are arbitrary real numbers, and
   the expectation functional is finite even with signed
   outcome weights; no component independence is assumed.
   Proof/definition method: Applies FiniteSum.finite_sum to
   coefficient times expect of each score, reusing the common
   finite list fold and the module's expect function.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition linear_expectation
    (components : list (R * (Outcome -> R))) : R :=
    FiniteSum.finite_sum (fun c => fst c * expect (snd c)) components.

  (* The covariance coefficient row is an ordinary list fold. *)
  (**
   [covariance_row] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: A row of the bilinear covariance form:
   for fixed score f it sums each component coefficient
   multiplied by Cov(f, component score).
   Exact declaration: Definition covariance_row (f : Outcome -> R) (components : list
   (R * (Outcome -> R))) : R := FiniteSum.finite_sum (fun c => fst c * covariance f
   (snd c)) components.
   Premises and side conditions: Coefficients and sample weights are real.
   This algebraic form needs no independence or positive
   semidefinite hypothesis to be defined.
   Proof/definition method: Uses FiniteSum.finite_sum and the
   already defined covariance, avoiding bespoke matrix-row
   recursions and allowing generic sum lemmas to prove bilinearity.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition covariance_row
    (f : Outcome -> R)
    (components : list (R * (Outcome -> R))) : R :=
    FiniteSum.finite_sum
      (fun c => fst c * covariance f (snd c)) components.

  (* The double covariance sum is a fold of coefficient-weighted
     covariance rows, reusing the row fold above. *)
  (**
   [covariance_quadratic_form] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: The finite bilinear composite-covariance form:
   sum over left components of their coefficients times
   the covariance row with the right component list.
   Exact declaration: Definition covariance_quadratic_form (left right : list (R *
   (Outcome -> R))) : R := FiniteSum.finite_sum (fun c => fst c * covariance_row (snd
   c) right) left.
   Premises and side conditions: Left and right lists can have different lengths;
   coefficients are arbitrary real values and independence
   is not assumed. Positive-semidefiniteness needs separate
   nonnegative normalized sample-weight premises.
   Proof/definition method: Reuses covariance_row and
   FiniteSum.finite_sum for the outer fold, corresponding
   to the standard weighted cross-covariance matrix product.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition covariance_quadratic_form
    (left right : list (R * (Outcome -> R))) : R :=
    FiniteSum.finite_sum
      (fun c => fst c * covariance_row (snd c) right) left.

  (**
   [expectation_of_general_weighted_sum] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma expectation_of_general_weighted_sum : forall
   components, expect (linear_combination components) = linear_expectation
   components.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization, definitional reduction;
   references include linear_combination, FiniteSum.finite_sum_ext,
   FiniteSum.finite_sum_scale..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma expectation_of_general_weighted_sum :
    forall components,
      expect (linear_combination components) =
        linear_expectation components.
  Proof.
    intros components.
    unfold linear_combination, linear_expectation, expect, sum_finite.
    transitivity (FiniteSum.finite_sum
      (fun x => FiniteSum.finite_sum
        (fun c => weight x * (fst c * snd c x)) components)
      samples).
    - apply FiniteSum.finite_sum_ext; intro x.
      symmetry; apply FiniteSum.finite_sum_scale.
    - rewrite FiniteSum.finite_sum_swap.
      apply FiniteSum.finite_sum_ext; intro c.
      transitivity (FiniteSum.finite_sum
        (fun x => fst c * (weight x * snd c x)) samples).
      + apply FiniteSum.finite_sum_ext; intro x; ring.
      + rewrite FiniteSum.finite_sum_scale; reflexivity.
  Qed.

  (* Covariance is linear in the second score argument because both
     finite expectations distribute over finite linear combinations.
     We prove this once with the generic finite-sum interchange laws,
     instead of repeating an induction over weighted score components.
     Unlike covariance with a nonzero constant, covariance with the
     zero-score linear combination needs no total-mass normalization. *)
  (**
   [covariance_of_general_weighted_second_unconditional] (lemma) — Finite
   weighted covariance over explicitly enumerated outcomes.
   Mathematical meaning: An arbitrary finite real-weighted composite
   has covariance equal to the corresponding weighted sum of component
   covariances. This bilinearity identity is algebraic and does not
   require the sample weights to total one.
   Exact checked proposition: forall f components,
   covariance f (linear_combination components) =
   covariance_row f components.
   Premises and side conditions: Outcome, samples and weight are the
   module's explicit parameters. The equality holds for arbitrary real
   weights, possibly negative or unnormalized; it does not interpret
   them as a probability distribution.
   Proof/definition method: Represent the product f times the linear
   combination as another mapped linear combination, use
   expectation_of_general_weighted_sum and finite_sum_map, then
   distribute the scalar expectation using finite_sum_scale and
   rewrite the difference using finite_sum_sub and real ring algebra.
   Library reuse: Stdlib.List.map, FiniteSum.finite_sum_map,
   finite_sum_scale, finite_sum_sub, finite_sum_ext,
   and the checked expectation_of_general_weighted_sum.
   Boundary: Exact finite algebra, not continuous covariance or
   empirical psychometric measurement assumptions.
   *)
  Lemma covariance_of_general_weighted_second_unconditional :
    forall f components,
      covariance f (linear_combination components) =
        covariance_row f components.
  Proof.
    intros f components.
    unfold covariance, covariance_row.
    rewrite expectation_of_general_weighted_sum.
    assert (Hproduct :
      expect (fun x => f x * linear_combination components x) =
        FiniteSum.finite_sum
          (fun c => fst c * expect (fun x => f x * snd c x))
          components).
    {
      transitivity (expect (linear_combination
        (map (fun c => (fst c, fun x => f x * snd c x)) components))).
      - apply expectation_ext; intro x.
        unfold linear_combination.
        rewrite FiniteSum.finite_sum_map.
        transitivity (FiniteSum.finite_sum
          (fun c => f x * (fst c * snd c x)) components).
        + rewrite FiniteSum.finite_sum_scale; reflexivity.
        + apply FiniteSum.finite_sum_ext; intro c.
          cbn [fst snd]; ring.
      - rewrite expectation_of_general_weighted_sum.
        unfold linear_expectation.
        rewrite FiniteSum.finite_sum_map.
        apply FiniteSum.finite_sum_ext; intro c; reflexivity.
    }
    rewrite Hproduct.
    unfold linear_expectation.
    rewrite <- FiniteSum.finite_sum_scale.
    rewrite <- FiniteSum.finite_sum_sub.
    apply FiniteSum.finite_sum_ext; intro c.
    unfold covariance; ring.
  Qed.

  (**
   [covariance_of_general_weighted_second] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma covariance_of_general_weighted_second : forall f
   components, total_mass = 1 -> covariance f (linear_combination components) =
   covariance_row f components.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Specialize the stronger checked
   covariance_of_general_weighted_second_unconditional lemma; the
   inherited total_mass = 1 premise is retained for theorem compatibility.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_of_general_weighted_second :
    forall f components,
      total_mass = 1 ->
      covariance f (linear_combination components) =
        covariance_row f components.
  Proof.
    intros f components _.
    apply covariance_of_general_weighted_second_unconditional.
  Qed.

  (**
   [covariance_of_general_weighted_sums_unconditional] (theorem) —
   Covariance bilinearity for two arbitrary finite composite scores.
   Mathematical meaning: For finite lists of coefficient-score pairs,
   the covariance between their linear combinations equals the full
   double weighted covariance sum. In particular, the identity is
   algebraically valid even when the outcome weights do not sum to one.
   Exact checked proposition: forall left right,
   covariance (linear_combination left) (linear_combination right) =
   covariance_quadratic_form left right.
   Premises and side conditions: The ambient Outcome, samples and
   weight are arbitrary, including signed or unnormalized real sample
   weights. Composite coefficients can have either sign, and component
   lists may contain duplicate scores. No independence is assumed.
   Proof/definition method: Use covariance symmetry and the stronger
   covariance_of_general_weighted_second_unconditional theorem for
   each component list. Finish with the generic FiniteSum.finite_sum_ext
   lemma rather than duplicating recursive list or matrix algebra.
   Library reuse: Stdlib.Reals, FiniteSum.finite_sum_ext,
   covariance_symmetric, and the already checked unconditional
   linearity in the second covariance argument.
   Boundary: This is a finite real-weighted algebraic covariance
   identity; it does not make signed weights a probability measure,
   establish nonnegative variances, or prove empirical correlations.
   *)
  Theorem covariance_of_general_weighted_sums_unconditional :
    forall left right,
      covariance (linear_combination left)
                 (linear_combination right) =
        covariance_quadratic_form left right.
  Proof.
    intros left right.
    rewrite (covariance_symmetric
      (linear_combination left) (linear_combination right)).
    rewrite (covariance_of_general_weighted_second_unconditional
      (linear_combination right) left).
    unfold covariance_row, covariance_quadratic_form.
    apply FiniteSum.finite_sum_ext; intro c.
    rewrite (covariance_symmetric (linear_combination right) (snd c)).
    rewrite (covariance_of_general_weighted_second_unconditional
      (snd c) right).
    reflexivity.
  Qed.

  (**
   [covariance_of_general_weighted_sums] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_of_general_weighted_sums : forall
   left right, total_mass = 1 -> covariance (linear_combination left)
   (linear_combination right) = covariance_quadratic_form left right.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Apply the stronger
   covariance_of_general_weighted_sums_unconditional theorem.
   The original total_mass = 1 premise and theorem type are preserved
   for compatibility with existing downstream proofs.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_of_general_weighted_sums :
    forall left right,
      total_mass = 1 ->
      covariance (linear_combination left)
                 (linear_combination right) =
        covariance_quadratic_form left right.
  Proof.
    intros left right _.
    apply covariance_of_general_weighted_sums_unconditional.
  Qed.

  (**
   [variance_of_general_weighted_sum_unconditional] (theorem) —
   The finite variance quadratic-form identity without mass assumptions.
   Mathematical meaning: A composite score's self-covariance is
   exactly the coefficient-weighted double sum of all pairwise
   component covariances, even for nonnormalized finite weights.
   Exact checked proposition: forall components,
   variance (linear_combination components) =
   covariance_quadratic_form components components.
   Premises and side conditions: No normalization or nonnegative
   outcome-mass hypothesis is required for the exact polynomial
   equality. Arbitrary real score coefficients and repeated entries
   are admitted. Under signed weights the result need not be
   nonnegative and should not be called a probabilistic variance.
   Proof/definition method: Expand variance into covariance f f and
   instantiate covariance_of_general_weighted_sums_unconditional
   with the same list on both sides; no new sum induction or
   specialized matrix manipulation.
   Library reuse: covariance_of_general_weighted_sums_unconditional,
   the existing variance and covariance_quadratic_form definitions,
   Stdlib.Reals and shared FiniteSum algebra.
   Boundary: An exact finite weighted sum-of-covariances identity,
   not a distributional, Gaussian or empirical psychometric claim.
   *)
  Theorem variance_of_general_weighted_sum_unconditional :
    forall components,
      variance (linear_combination components) =
        covariance_quadratic_form components components.
  Proof.
    intros components.
    unfold variance.
    apply covariance_of_general_weighted_sums_unconditional.
  Qed.

  (**
   [variance_of_general_weighted_sum] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: For a finite composite score with arbitrary component
   coefficients, its variance equals the finite double weighted
   covariance sum, the quadratic-form identity Var(sum a_i X_i)
   = sum_i sum_j a_i a_j Cov(X_i,X_j).
   Exact checked proposition: Theorem variance_of_general_weighted_sum : forall
   components, total_mass = 1 -> variance (linear_combination components) =
   covariance_quadratic_form components components.
   Premises and side conditions: The checked public statement explicitly assumes
   total_mass=1 over sample occurrences. The score coefficients
   may be signed, component scores need not be independent, and
   the component list may repeat scores. Weight nonnegativity is
   not used for this algebraic equality.
   Proof/definition method: Apply the stronger
   variance_of_general_weighted_sum_unconditional theorem.
   The original total_mass = 1 premise remains in the public type
   to avoid changing any previously checked statement.
   Library reuse: FiniteSum.finite_sum, covariance_of_general_weighted_sums,
   linear_combination, covariance_quadratic_form and Stdlib.Reals.
   Boundary: A finite weighted outcome model, not an assertion
   about a continuum distribution or actual IQ test covariance;
   empirical covariance values and model fit are not proved.
*)
  Theorem variance_of_general_weighted_sum :
    forall components,
      total_mass = 1 ->
      variance (linear_combination components) =
        covariance_quadratic_form components components.
  Proof.
    intros components _.
    apply variance_of_general_weighted_sum_unconditional.
  Qed.

  (**
   [covariance_quadratic_form_nonnegative] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Theorem covariance_quadratic_form_nonnegative : forall
   components, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> 0 <=
   covariance_quadratic_form components components.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include variance_nonnegative.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_quadratic_form_nonnegative :
    forall components,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <= covariance_quadratic_form components components.
  Proof.
    intros components Hmass Hweights.
    rewrite <- (variance_of_general_weighted_sum components Hmass).
    apply variance_nonnegative; assumption.
  Qed.


  (* Concrete bridge from finite covariance algebra to the report's
     two-/three-test average-correlation identities.  Each statement
     refers to the same finite reference distribution. *)

  (**
   [mean_of_centered_standardized_score] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem mean_of_centered_standardized_score : forall f
   sd, total_mass = 1 -> sd <> 0 -> expect (fun x => (f x - expect f) / sd) = 0.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; explicit nonzero or strict-positive numerical conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   expectation_ext, expectation_scale., centered_score_has_zero_expectation.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem mean_of_centered_standardized_score :
    forall f sd,
      total_mass = 1 -> sd <> 0 ->
      expect (fun x => (f x - expect f) / sd) = 0.
  Proof.
    intros f sd Hmass Hsd.
    transitivity
      (expect (fun x => (/sd) * (f x - expect f))).
    - apply expectation_ext; intro x; unfold Rdiv; ring.
    - rewrite expectation_scale.
      rewrite (centered_score_has_zero_expectation f Hmass).
      ring.
  Qed.

  (**
   [mean_of_iq_reporting_scale] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Theorem mean_of_iq_reporting_scale : forall f sd scale,
   total_mass = 1 -> sd <> 0 -> expect (fun x => 100 + scale * ((f x - expect f) /
   sd)) = 100.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; explicit nonzero or strict-positive numerical conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   expectation_ext, expectation_affine, mean_of_centered_standardized_score.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem mean_of_iq_reporting_scale :
    forall f sd scale,
      total_mass = 1 -> sd <> 0 ->
      expect (fun x => 100 + scale * ((f x - expect f) / sd)) = 100.
  Proof.
    intros f sd scale Hmass Hsd.
    transitivity
      (expect (fun x => scale * ((f x - expect f) / sd) + 100)).
    - apply expectation_ext; intro x; ring.
    - rewrite (expectation_affine
        (fun x => (f x - expect f) / sd) scale 100 Hmass).
      rewrite (mean_of_centered_standardized_score f sd Hmass Hsd).
      ring.
  Qed.

  (**
   [covariance_invariant_under_both_shifts] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_invariant_under_both_shifts : forall
   f g a b, total_mass = 1 -> covariance (fun x => f x + a) (fun x => g x + b) =
   covariance f g.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include
   covariance_invariant_under_first_shift, covariance_invariant_under_second_shift,
   Hmass..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_invariant_under_both_shifts :
    forall f g a b,
      total_mass = 1 ->
      covariance (fun x => f x + a) (fun x => g x + b)
      = covariance f g.
  Proof.
    intros f g a b Hmass.
    rewrite (covariance_invariant_under_first_shift
      f (fun x => g x + b) a Hmass).
    apply covariance_invariant_under_second_shift; exact Hmass.
  Qed.

  (**
   [covariance_of_centered_standardized_scores] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_of_centered_standardized_scores :
   forall f g sd_f sd_g, total_mass = 1 -> sd_f <> 0 -> sd_g <> 0 -> covariance (fun
   x => (f x - expect f) / sd_f) (fun x => (g x - expect g) / sd_g) = covariance f g
   / (sd_f * sd_g).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; explicit nonzero or strict-positive numerical conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, polynomial real arithmetic (Psatz), ring/field
   normalization; references include covariance_extensional, covariance_scale_first,
   covariance_invariant_under_both_shifts.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_of_centered_standardized_scores :
    forall f g sd_f sd_g,
      total_mass = 1 ->
      sd_f <> 0 -> sd_g <> 0 ->
      covariance
        (fun x => (f x - expect f) / sd_f)
        (fun x => (g x - expect g) / sd_g)
      = covariance f g / (sd_f * sd_g).
  Proof.
    intros f g sd_f sd_g Hmass Hsf Hsg.
    transitivity
      (covariance
        (fun x => (/sd_f) * (f x + (- expect f)))
        (fun x => (/sd_g) * (g x + (- expect g)))).
    - apply covariance_extensional;
        intro x; unfold Rdiv; ring.
    - rewrite covariance_scale_first, covariance_scale_second.
      rewrite (covariance_invariant_under_both_shifts
        f g (- expect f) (- expect g) Hmass).
      field; nra.
  Qed.

  (**
   [self_covariance_of_standardized_score] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem self_covariance_of_standardized_score : forall
   f sd, total_mass = 1 -> sd <> 0 -> variance f = sd * sd -> covariance (fun x => (f
   x - expect f) / sd) (fun x => (f x - expect f) / sd) = 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; explicit nonzero or strict-positive numerical conditions; stated
   unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, polynomial
   real arithmetic (Psatz), ring/field normalization; references include
   covariance_of_centered_standardized_scores.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem self_covariance_of_standardized_score :
    forall f sd,
      total_mass = 1 -> sd <> 0 ->
      variance f = sd * sd ->
      covariance
        (fun x => (f x - expect f) / sd)
        (fun x => (f x - expect f) / sd) = 1.
  Proof.
    intros f sd Hmass Hsd Hvar.
    rewrite (covariance_of_centered_standardized_scores
      f f sd sd Hmass Hsd Hsd).
    change (variance f / (sd * sd) = 1).
    rewrite Hvar; field; nra.
  Qed.

  (**
   [variance_of_three_score_average] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_three_score_average : forall f g h,
   variance (fun x => (f x + g x + h x) / 3) = (variance f + variance g + variance h
   + 2 * covariance f g + 2 * covariance f h + 2 * covariance g h) / 9.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   variance_extensional, variance_of_scaled_score., variance_of_two_score_sum..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_three_score_average :
    forall f g h,
      variance (fun x => (f x + g x + h x) / 3) =
      (variance f + variance g + variance h +
       2 * covariance f g + 2 * covariance f h +
       2 * covariance g h) / 9.
  Proof.
    intros f g h.
    transitivity
      (variance (fun x => (/3) * ((f x + g x) + h x))).
    - apply variance_extensional; intro x; unfold Rdiv; ring.
    - rewrite variance_of_scaled_score.
      rewrite variance_of_two_score_sum.
      rewrite variance_of_two_score_sum.
      rewrite covariance_add_first.
      field.
  Qed.

  (**
   [variance_of_three_standardized_score_average] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_three_standardized_score_average :
   forall f g h rho, variance f = 1 -> variance g = 1 -> variance h = 1 -> covariance
   f g + covariance f h + covariance g h = 3 * rho -> variance (fun x => (f x + g x +
   h x) / 3) = (1 + 2 * rho) / 3.
   Premises and side conditions: The displayed hypotheses include stated
   unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, linear real
   arithmetic (Lra), ring/field normalization; references include
   variance_of_three_score_average.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_three_standardized_score_average :
    forall f g h rho,
      variance f = 1 -> variance g = 1 -> variance h = 1 ->
      covariance f g + covariance f h + covariance g h = 3 * rho ->
      variance (fun x => (f x + g x + h x) / 3) =
        (1 + 2 * rho) / 3.
  Proof.
    intros f g h rho Hf Hg Hh Hpair.
    rewrite variance_of_three_score_average, Hf, Hg, Hh.
    field_simplify; lra.
  Qed.

  (**
   [variance_of_two_standardized_score_average] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_two_standardized_score_average :
   forall f g rho, variance f = 1 -> variance g = 1 -> covariance f g = rho ->
   variance (fun x => (f x + g x) / 2) = (1 + rho) / 2.
   Premises and side conditions: The displayed hypotheses include stated
   unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include variance_of_two_unit_variance_average.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_two_standardized_score_average :
    forall f g rho,
      variance f = 1 -> variance g = 1 ->
      covariance f g = rho ->
      variance (fun x => (f x + g x) / 2) =
        (1 + rho) / 2.
  Proof.
    intros f g rho Hf Hg Hcov.
    rewrite (variance_of_two_unit_variance_average f g Hf Hg).
    rewrite Hcov; reflexivity.
  Qed.


  (* The full equal-weight battery identity.  The off-diagonal sum counts
     each distinct unordered test pair exactly once, regardless of whether
     pairwise correlations are equal. *)

  (* Standard-library list fold for a sum of score functions. *)
  (**
   [sum_scores] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Defines sum scores using explicit Rocq operations, so later
   theorems can refer to one stable mathematical object.
   Exact declaration: Definition sum_scores (fs : list (Outcome -> R)) (x : Outcome)
   : R := FiniteSum.finite_sum (fun f => f x) fs.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition sum_scores (fs : list (Outcome -> R)) (x : Outcome) : R :=
    FiniteSum.finite_sum (fun f => f x) fs.

  (* Unweighted covariance matrix row: a standard list fold. *)
  (**
   [covariance_row_sum] (definition) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Defines covariance row sum using explicit Rocq operations,
   so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition covariance_row_sum (f : Outcome -> R) (fs : list
   (Outcome -> R)) : R := FiniteSum.finite_sum (covariance f) fs.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition covariance_row_sum
      (f : Outcome -> R) (fs : list (Outcome -> R)) : R :=
    FiniteSum.finite_sum (covariance f) fs.

  (* Double covariance sum is a fold over the row-fold operator. *)
  (**
   [covariance_double_sum] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines covariance double sum using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition covariance_double_sum (fs gs : list (Outcome -> R))
   : R := FiniteSum.finite_sum (fun f => covariance_row_sum f gs) fs.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition covariance_double_sum
      (fs gs : list (Outcome -> R)) : R :=
    FiniteSum.finite_sum (fun f => covariance_row_sum f gs) fs.

  (* Sum the covariance-matrix diagonal using Stdlib.List. *)
  (**
   [diagonal_variance_sum] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines diagonal variance sum using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition diagonal_variance_sum (fs : list (Outcome -> R)) : R
   := FiniteSum.finite_sum variance fs.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition diagonal_variance_sum
      (fs : list (Outcome -> R)) : R :=
    FiniteSum.finite_sum variance fs.

  (**
   [unordered_covariance_sum] (fixpoint) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines unordered covariance sum using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Fixpoint unordered_covariance_sum (fs : list (Outcome -> R)) :
   R := match fs with | [] => 0 | f :: tl => covariance_row_sum f tl +
   unordered_covariance_sum tl end.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Fixpoint unordered_covariance_sum
      (fs : list (Outcome -> R)) : R :=
    match fs with
    | [] => 0
    | f :: tl => covariance_row_sum f tl +
                 unordered_covariance_sum tl
    end.

  (**
   [covariance_double_sum_second_cons] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma covariance_double_sum_second_cons : forall fs f
   gs, covariance_double_sum fs (f :: gs) = covariance_row_sum f fs +
   covariance_double_sum fs gs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include covariance_double_sum,
   FiniteSum.finite_sum_add., FiniteSum.finite_sum_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_double_sum_second_cons :
    forall fs f gs,
      covariance_double_sum fs (f :: gs) =
        covariance_row_sum f fs + covariance_double_sum fs gs.
  Proof.
    intros fs f gs.
    unfold covariance_double_sum, covariance_row_sum.
    change (FiniteSum.finite_sum
      (fun g => covariance g f +
        FiniteSum.finite_sum (covariance g) gs) fs =
      FiniteSum.finite_sum (covariance f) fs +
      FiniteSum.finite_sum
        (fun g => FiniteSum.finite_sum (covariance g) gs) fs).
    rewrite FiniteSum.finite_sum_add.
    f_equal.
    apply FiniteSum.finite_sum_ext; intro g.
    apply covariance_symmetric.
  Qed.

  (* Symmetry of the double covariance sum is a direct consequence
     of FiniteSum.finite_sum_swap and the already proved scalar
     covariance symmetry. No additional list induction is needed. *)
  (**
   [covariance_double_sum_symmetric] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma covariance_double_sum_symmetric : forall fs gs,
   covariance_double_sum fs gs = covariance_double_sum gs fs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include covariance_double_sum,
   FiniteSum.finite_sum_swap, FiniteSum.finite_sum_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_double_sum_symmetric :
    forall fs gs,
      covariance_double_sum fs gs = covariance_double_sum gs fs.
  Proof.
    intros fs gs.
    unfold covariance_double_sum, covariance_row_sum.
    rewrite (FiniteSum.finite_sum_swap fs gs covariance).
    apply FiniteSum.finite_sum_ext; intro g.
    apply FiniteSum.finite_sum_ext; intro f.
    apply covariance_symmetric.
  Qed.

  (**
   [double_sum_diagonal_off_diagonal] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma double_sum_diagonal_off_diagonal : forall fs,
   covariance_double_sum fs fs = diagonal_variance_sum fs + 2 *
   unordered_covariance_sum fs.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, ring/field normalization; references include
   covariance_double_sum_second_cons, variance.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma double_sum_diagonal_off_diagonal :
    forall fs,
      covariance_double_sum fs fs =
      diagonal_variance_sum fs + 2 * unordered_covariance_sum fs.
  Proof.
    induction fs as [|f fs IH].
    - change (0 = 0 + 2 * 0); ring.
    - change
        (covariance_row_sum f (f :: fs) +
         covariance_double_sum fs (f :: fs) =
         variance f + diagonal_variance_sum fs +
           2 * (covariance_row_sum f fs +
                unordered_covariance_sum fs)).
      rewrite (covariance_double_sum_second_cons fs f fs).
      rewrite IH.
      change
        ((covariance f f + covariance_row_sum f fs) +
          (covariance_row_sum f fs +
            (diagonal_variance_sum fs +
             2 * unordered_covariance_sum fs)) =
         variance f + diagonal_variance_sum fs +
           2 * (covariance_row_sum f fs +
                unordered_covariance_sum fs)).
      unfold variance; ring.
  Qed.

  (* An unweighted score list is just a list of unit-weight
     components. Stdlib.List.map and shared finite_sum_map give the
     interpretation without a second recursive score evaluator. *)
  (**
   [unweighted_scores_as_linear_combination] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Relates finite outcome weights to the stated marginal,
   joint, or enumerated-event quantity.
   Exact checked proposition: Lemma unweighted_scores_as_linear_combination : forall
   fs x, sum_scores fs x = linear_combination (map (fun f => (1, f)) fs) x.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization, definitional reduction;
   references include sum_scores, FiniteSum.finite_sum_map.,
   FiniteSum.finite_sum_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma unweighted_scores_as_linear_combination :
    forall fs x,
      sum_scores fs x =
        linear_combination (map (fun f => (1, f)) fs) x.
  Proof.
    intros fs x.
    unfold sum_scores, linear_combination.
    rewrite FiniteSum.finite_sum_map.
    apply FiniteSum.finite_sum_ext; intro f.
    simpl; ring.
  Qed.

  (**
   [unweighted_covariance_row_as_weighted] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma unweighted_covariance_row_as_weighted : forall f
   fs, covariance_row_sum f fs = covariance_row f (map (fun g => (1, g)) fs).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization, definitional reduction;
   references include covariance_row_sum, FiniteSum.finite_sum_map.,
   FiniteSum.finite_sum_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma unweighted_covariance_row_as_weighted :
    forall f fs,
      covariance_row_sum f fs =
        covariance_row f (map (fun g => (1, g)) fs).
  Proof.
    intros f fs.
    unfold covariance_row_sum, covariance_row.
    rewrite FiniteSum.finite_sum_map.
    apply FiniteSum.finite_sum_ext; intro g.
    simpl; ring.
  Qed.

  (**
   [covariance_with_sum_scores_unconditional] (lemma) — Covariance
   of a score with an unweighted finite list-sum of other scores.
   Mathematical meaning: Covariance distributes over an unweighted
   finite sum: Cov(f, sum_i g_i) = sum_i Cov(f,g_i), even when the
   real-valued sample weights do not sum to one.
   Exact checked proposition: forall f fs,
   covariance f (sum_scores fs) = covariance_row_sum f fs.
   Premises and side conditions: Arbitrary finite sample enumeration,
   signed weights and real score functions are allowed. The score
   list may contain repetitions. No unit total mass, independence
   or nonnegativity assumption is made in this algebraic equality.
   Proof/definition method: Reuse the established representation of
   unweighted scores as a Stdlib.List.map of unit-coefficient pairs,
   then invoke covariance_of_general_weighted_second_unconditional
   and unweighted_covariance_row_as_weighted.
   Library reuse: Stdlib.List.map, covariance_extensional,
   unweighted_scores_as_linear_combination,
   covariance_of_general_weighted_second_unconditional and
   unweighted_covariance_row_as_weighted. No new list induction.
   Boundary: Algebraic finite covariance of a list sum; signed
   outcome weights need not form a probability measure.
   *)
  Lemma covariance_with_sum_scores_unconditional :
    forall f fs,
      covariance f (sum_scores fs) = covariance_row_sum f fs.
  Proof.
    intros f fs.
    transitivity
      (covariance f
        (linear_combination (map (fun g => (1, g)) fs))).
    - apply covariance_extensional.
      + intro x; reflexivity.
      + intro x; apply unweighted_scores_as_linear_combination.
    - rewrite (covariance_of_general_weighted_second_unconditional
        f (map (fun g => (1, g)) fs)).
      symmetry; apply unweighted_covariance_row_as_weighted.
  Qed.

  (**
   [covariance_with_sum_scores] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma covariance_with_sum_scores : forall f fs,
   total_mass = 1 -> covariance f (sum_scores fs) = covariance_row_sum f fs.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Invoke the general covariance_with_sum_scores_unconditional
   lemma, preserving the original total_mass = 1 premise in the
   public statement without duplicating the linearity argument.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_with_sum_scores :
    forall f fs, total_mass = 1 ->
      covariance f (sum_scores fs) = covariance_row_sum f fs.
  Proof.
    intros f fs _.
    apply covariance_with_sum_scores_unconditional.
  Qed.

  (**
   [covariance_of_sum_scores_unconditional] (lemma) — Bilinearity
   of covariance across two finite unweighted score lists.
   Mathematical meaning: The covariance of the sums of two
   finite score lists is the double sum of every pairwise
   component covariance, without a sample normalization premise.
   Exact checked proposition: forall fs gs,
   covariance (sum_scores fs) (sum_scores gs) =
   covariance_double_sum fs gs.
   Premises and side conditions: Score lists may have unequal length,
   contain repeats or be empty; sample weights and score values may
   be signed. No independence or unit-mass hypothesis is required
   for equality of the real-valued expressions.
   Proof/definition method: Use covariance symmetry, apply
   covariance_with_sum_scores_unconditional to each list in turn,
   and use FiniteSum.finite_sum_ext to align the double sum.
   Library reuse: covariance_symmetric,
   covariance_with_sum_scores_unconditional,
   FiniteSum.finite_sum_ext and the existing sum/covariance aliases.
   Boundary: Algebraic finite-score list covariance; not a
   probabilistic or empirical correlation assumption.
   *)
  Lemma covariance_of_sum_scores_unconditional :
    forall fs gs,
      covariance (sum_scores fs) (sum_scores gs) =
        covariance_double_sum fs gs.
  Proof.
    intros fs gs.
    rewrite (covariance_symmetric (sum_scores fs) (sum_scores gs)).
    rewrite (covariance_with_sum_scores_unconditional
      (sum_scores gs) fs).
    unfold covariance_row_sum, covariance_double_sum.
    apply FiniteSum.finite_sum_ext; intro f.
    rewrite (covariance_symmetric (sum_scores gs) f).
    apply covariance_with_sum_scores_unconditional.
  Qed.

  (**
   [covariance_of_sum_scores] (lemma) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma covariance_of_sum_scores : forall fs gs,
   total_mass = 1 -> covariance (sum_scores fs) (sum_scores gs) =
   covariance_double_sum fs gs.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Invoke the stronger covariance_of_sum_scores_unconditional
   lemma; the original unit-mass premise and proposition remain
   unchanged for downstream source compatibility.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_of_sum_scores :
    forall fs gs, total_mass = 1 ->
      covariance (sum_scores fs) (sum_scores gs) =
        covariance_double_sum fs gs.
  Proof.
    intros fs gs _.
    apply covariance_of_sum_scores_unconditional.
  Qed.

  (**
   [variance_of_unweighted_sum_unconditional] (theorem) — Finite
   variance of an arbitrary unweighted score-list composite.
   Mathematical meaning: The variance of a sum of listed scores
   equals the double sum of the score covariances, even for
   unnormalized or signed sample weights.
   Exact checked proposition: forall fs,
   variance (sum_scores fs) = covariance_double_sum fs fs.
   Premises and side conditions: Any finite list of real scores,
   including duplicate scores, with arbitrary real sample
   weights. This is an algebraic identity; nonnegative variance
   requires a valid normalized nonnegative sample distribution.
   Proof/definition method: Expand variance as self-covariance
   and specialize covariance_of_sum_scores_unconditional with
   identical score lists, without a separate induction.
   Library reuse: The checked unconditional score-list covariance
   identity and the existing variance/covariance_double_sum
   definitions backed by FiniteSum.
   Boundary: A finite real-valued quadratic expression, not
   proof of empirical score covariance or Gaussianity.
   *)
  Theorem variance_of_unweighted_sum_unconditional :
    forall fs,
      variance (sum_scores fs) = covariance_double_sum fs fs.
  Proof.
    intro fs.
    unfold variance.
    apply covariance_of_sum_scores_unconditional.
  Qed.

  (**
   [variance_of_unweighted_sum] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_unweighted_sum : forall fs,
   total_mass = 1 -> variance (sum_scores fs) = covariance_double_sum fs fs.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Apply the general variance_of_unweighted_sum_unconditional
   theorem. The original total_mass = 1 premise remains part
   of the public theorem signature even though not used here.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_unweighted_sum :
    forall fs, total_mass = 1 ->
      variance (sum_scores fs) = covariance_double_sum fs fs.
  Proof.
    intros fs _.
    apply variance_of_unweighted_sum_unconditional.
  Qed.

  (**
   [variance_of_rescaled_unweighted_sum] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_rescaled_unweighted_sum : forall fs
   n, total_mass = 1 -> n <> 0 -> variance (fun x => sum_scores fs x / n) =
   (diagonal_variance_sum fs + 2 * unordered_covariance_sum fs) / (n * n).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; explicit nonzero or strict-positive numerical conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra), ring/field
   normalization; references include variance_extensional, variance_of_scaled_score.,
   variance_of_unweighted_sum.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_rescaled_unweighted_sum :
    forall fs n,
      total_mass = 1 -> n <> 0 ->
      variance (fun x => sum_scores fs x / n) =
        (diagonal_variance_sum fs + 2 * unordered_covariance_sum fs)
          / (n * n).
  Proof.
    intros fs n Hmass Hn.
    transitivity (variance (fun x => (/n) * sum_scores fs x)).
    - apply variance_extensional; intro x.
      unfold Rdiv; ring.
    - rewrite variance_of_scaled_score.
      rewrite (variance_of_unweighted_sum fs Hmass).
      rewrite double_sum_diagonal_off_diagonal.
      field; lra.
  Qed.

  (**
   [diagonal_variance_sum_of_unit_scores] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Lemma diagonal_variance_sum_of_unit_scores : forall fs,
   (forall f, In f fs -> variance f = 1) -> diagonal_variance_sum fs = INR (length
   fs).
   Premises and side conditions: The displayed hypotheses include dimension/length
   compatibility where required; sample or list membership; stated unit-variance
   conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   diagonal_variance_sum., FiniteSum.finite_sum_ext_in., FiniteSum.finite_sum_const.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma diagonal_variance_sum_of_unit_scores :
    forall fs,
      (forall f, In f fs -> variance f = 1) ->
      diagonal_variance_sum fs = INR (length fs).
  Proof.
    intros fs Hunit.
    unfold diagonal_variance_sum.
    transitivity (FiniteSum.finite_sum (fun _ => 1) fs).
    - apply FiniteSum.finite_sum_ext_in.
      intros f Hin; apply Hunit; exact Hin.
    - rewrite FiniteSum.finite_sum_const; ring.
  Qed.

  (**
   [equal_weight_variance_from_finite_covariances] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem equal_weight_variance_from_finite_covariances :
   forall fs n rho, total_mass = 1 -> n = INR (length fs) -> 1 < n -> (forall f, In f
   fs -> variance f = 1) -> 2 * unordered_covariance_sum fs = n * (n - 1) * rho ->
   variance (fun x => sum_scores fs x / n) = rho + (1 - rho) / n.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; dimension/length compatibility where required; sample or list membership;
   stated unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, linear real
   arithmetic (Lra), polynomial real arithmetic (Psatz), ring/field normalization;
   references include variance_of_rescaled_unweighted_sum,
   diagonal_variance_sum_of_unit_scores, Hpairs..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem equal_weight_variance_from_finite_covariances :
    forall fs n rho,
      total_mass = 1 ->
      n = INR (length fs) ->
      1 < n ->
      (forall f, In f fs -> variance f = 1) ->
      2 * unordered_covariance_sum fs = n * (n - 1) * rho ->
      variance (fun x => sum_scores fs x / n) =
        rho + (1 - rho) / n.
  Proof.
    intros fs n rho Hmass Hlength Hn Hunit Hpairs.
    rewrite (variance_of_rescaled_unweighted_sum fs n Hmass)
      by lra.
    rewrite (diagonal_variance_sum_of_unit_scores fs Hunit).
    rewrite <- Hlength.
    rewrite Hpairs.
    field; nra.
  Qed.


  (* Concrete matrix notation: a covariance matrix is represented as a
     rectangular list of rows, its coefficient vector as a list of real
     weights.  No matrix equalities are postulated: all entries are the
     finite-space covariance defined above. *)

  (* List.combine gives the library's standard zip/truncate semantics;
     map and fold_right perform the inner product without bespoke recursion. *)
  (**
   [vector_dot] (definition) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Defines vector dot using explicit Rocq operations, so later
   theorems can refer to one stable mathematical object.
   Exact declaration: Definition vector_dot (xs ys : list R) : R :=
   FiniteSum.finite_sum (fun p => fst p * snd p) (combine xs ys).
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition vector_dot (xs ys : list R) : R :=
    FiniteSum.finite_sum
      (fun p => fst p * snd p) (combine xs ys).

  (**
   [covariance_cross_matrix] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines covariance cross matrix using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition covariance_cross_matrix (left right : list (R *
   (Outcome -> R))) : list (list R) := map (fun c => map (fun d => covariance (snd c)
   (snd d)) right) left.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition covariance_cross_matrix
    (left right : list (R * (Outcome -> R))) : list (list R) :=
    map (fun c => map
      (fun d => covariance (snd c) (snd d)) right) left.

  (**
   [covariance_matrix] (definition) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Defines covariance matrix using explicit Rocq operations, so
   later theorems can refer to one stable mathematical object.
   Exact declaration: Definition covariance_matrix (components : list (R * (Outcome
   -> R))) : list (list R) := covariance_cross_matrix components components.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition covariance_matrix
    (components : list (R * (Outcome -> R))) : list (list R) :=
    covariance_cross_matrix components components.

  (**
   [matrix_bilinear_form] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines matrix bilinear form using explicit Rocq operations,
   so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition matrix_bilinear_form (left_coeffs right_coeffs :
   list R) (matrix : list (list R)) : R := vector_dot left_coeffs (map (vector_dot
   right_coeffs) matrix).
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition matrix_bilinear_form
    (left_coeffs right_coeffs : list R)
    (matrix : list (list R)) : R :=
    vector_dot left_coeffs (map (vector_dot right_coeffs) matrix).

  (**
   [matrix_quadratic_form] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines matrix quadratic form using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition matrix_quadratic_form (coeffs : list R) (matrix :
   list (list R)) : R := matrix_bilinear_form coeffs coeffs matrix.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition matrix_quadratic_form
    (coeffs : list R) (matrix : list (list R)) : R :=
    matrix_bilinear_form coeffs coeffs matrix.

  (**
   [covariance_row_as_vector_dot] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma covariance_row_as_vector_dot : forall f
   components, vector_dot (map fst components) (map (fun c => covariance f (snd c))
   components) = covariance_row f components.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Use FiniteSum.finite_sum_zip_map to eliminate the
   aligned List.combine of two List.map projections; then extensionality.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_row_as_vector_dot :
    forall f components,
      vector_dot (map fst components)
        (map (fun c => covariance f (snd c)) components) =
      covariance_row f components.
  Proof.
    intros f components.
    unfold vector_dot, covariance_row.
    rewrite FiniteSum.finite_sum_zip_map.
    apply FiniteSum.finite_sum_ext.
    intro c; reflexivity.
  Qed.

  (**
   [covariance_double_sum_as_matrix_product] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma covariance_double_sum_as_matrix_product : forall
   left right, matrix_bilinear_form (map fst left) (map fst right)
   (covariance_cross_matrix left right) = covariance_quadratic_form left right.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Flatten the nested Stdlib.List.map with map_map,
   use the generic FiniteSum.finite_sum_zip_map and covariance_row_as_vector_dot.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_double_sum_as_matrix_product :
    forall left right,
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      covariance_quadratic_form left right.
  Proof.
    intros left right.
    unfold matrix_bilinear_form, covariance_cross_matrix,
      covariance_quadratic_form.
    rewrite map_map.
    unfold vector_dot at 1.
    rewrite FiniteSum.finite_sum_zip_map.
    apply FiniteSum.finite_sum_ext.
    intro c; simpl.
    rewrite (covariance_row_as_vector_dot (snd c) right).
    reflexivity.
  Qed.

  (**
   [covariance_matrix_quadratic_form_identity] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Theorem covariance_matrix_quadratic_form_identity :
   forall components, matrix_quadratic_form (map fst components) (covariance_matrix
   components) = covariance_quadratic_form components components.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include matrix_quadratic_form,
   covariance_double_sum_as_matrix_product..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_matrix_quadratic_form_identity :
    forall components,
      matrix_quadratic_form (map fst components)
        (covariance_matrix components) =
      covariance_quadratic_form components components.
  Proof.
    intro components.
    unfold matrix_quadratic_form, covariance_matrix.
    apply covariance_double_sum_as_matrix_product.
  Qed.

  (**
   [covariance_cross_matrix_bilinear_identity_unconditional] (theorem) —
   Matrix representation of covariance between two finite composites.
   Mathematical meaning: The cross-covariance matrix evaluated against
   both coefficient lists equals the covariance of the corresponding
   composite score functions, even for unnormalized sample weights.
   Exact checked proposition: forall left right,
   matrix_bilinear_form (map fst left) (map fst right)
     (covariance_cross_matrix left right) =
   covariance (linear_combination left) (linear_combination right).
   Premises and side conditions: Only the finite outcome enumeration
   and arbitrary real-valued weight and score functions are used.
   The component lists may differ in length and contain repeats;
   sample weights and coefficients may be signed. No probability,
   independence or total_mass = 1 hypothesis is assumed.
   Proof/definition method: Rewrite the matrix product with the
   existing covariance_double_sum_as_matrix_product theorem, then
   apply covariance_of_general_weighted_sums_unconditional.
   Library reuse: Stdlib.List.map and combine, shared finite sums,
   covariance_double_sum_as_matrix_product, and the generic
   unconditional weighted-composite covariance identity.
   Boundary: A finite algebraic matrix representation; without
   nonnegative normalized sample weights, covariance matrices
   need not be positive semidefinite in a probabilistic sense.
   *)
  Theorem covariance_cross_matrix_bilinear_identity_unconditional :
    forall left right,
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      covariance (linear_combination left) (linear_combination right).
  Proof.
    intros left right.
    rewrite covariance_double_sum_as_matrix_product.
    symmetry.
    apply covariance_of_general_weighted_sums_unconditional.
  Qed.

  (**
   [covariance_cross_matrix_bilinear_identity] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Theorem covariance_cross_matrix_bilinear_identity :
   forall left right, total_mass = 1 -> matrix_bilinear_form (map fst left) (map fst
   right) (covariance_cross_matrix left right) = covariance (linear_combination left)
   (linear_combination right).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Apply the unconditional
   covariance_cross_matrix_bilinear_identity_unconditional theorem.
   The original total_mass = 1 premise is retained verbatim for
   compatibility but is not needed for this algebraic equality.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_cross_matrix_bilinear_identity :
    forall left right,
      total_mass = 1 ->
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      covariance (linear_combination left) (linear_combination right).
  Proof.
    intros left right _.
    apply covariance_cross_matrix_bilinear_identity_unconditional.
  Qed.

  (* The coefficient-vector bilinear form of a cross-covariance
     matrix is symmetric under exchanging both score bases.
     The proof reuses the checked finite-basis representation and
     covariance symmetry instead of implementing a matrix transpose. *)
  (**
   [covariance_cross_matrix_bilinear_swap_unconditional] (theorem) —
   Swap invariance of a real cross-covariance bilinear form.
   Mathematical meaning: Swapping the component lists while
   transposing which covariance cross-matrix is constructed leaves
   the evaluated bilinear form unchanged.
   Exact checked proposition: forall left right,
   matrix_bilinear_form (map fst left) (map fst right)
     (covariance_cross_matrix left right) =
   matrix_bilinear_form (map fst right) (map fst left)
     (covariance_cross_matrix right left).
   Premises and side conditions: Arbitrary finite lists of real
   coefficient-score pairs, signed or unnormalized outcome weights,
   and duplicated scores are allowed. No mass normalization,
   independence, positivity or matrix symmetry is assumed.
   Proof/definition method: Apply the unconditional matrix-to-
   covariance identity in both orientations and then invoke
   covariance_symmetric. No matrix transpose implementation or
   specialized list induction is needed.
   Library reuse: covariance_cross_matrix_bilinear_identity_unconditional,
   covariance_symmetric, and Stdlib.Reals.
   Boundary: Equality of explicitly evaluated real bilinear forms,
   not an assertion of strict matrix positive definiteness.
   *)
  Theorem covariance_cross_matrix_bilinear_swap_unconditional :
    forall left right,
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      matrix_bilinear_form (map fst right) (map fst left)
        (covariance_cross_matrix right left).
  Proof.
    intros left right.
    rewrite (covariance_cross_matrix_bilinear_identity_unconditional
      left right).
    rewrite (covariance_cross_matrix_bilinear_identity_unconditional
      right left).
    apply covariance_symmetric.
  Qed.

  (**
   [covariance_cross_matrix_bilinear_swap] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Theorem covariance_cross_matrix_bilinear_swap : forall
   left right, total_mass = 1 -> matrix_bilinear_form (map fst left) (map fst right)
   (covariance_cross_matrix left right) = matrix_bilinear_form (map fst right) (map
   fst left) (covariance_cross_matrix right left).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Apply the stronger
   covariance_cross_matrix_bilinear_swap_unconditional theorem.
   The original normalization hypothesis remains part of the theorem
   statement; no extra symmetry or matrix transpose proof is needed.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_cross_matrix_bilinear_swap :
    forall left right,
      total_mass = 1 ->
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      matrix_bilinear_form (map fst right) (map fst left)
        (covariance_cross_matrix right left).
  Proof.
    intros left right _.
    apply covariance_cross_matrix_bilinear_swap_unconditional.
  Qed.

  (**
   [covariance_matrix_quadratic_form_is_variance_unconditional] (theorem) —
   Matrix quadratic-form equality for a finite weighted score.
   Mathematical meaning: Evaluating a composite's covariance matrix
   against its coefficient list yields exactly that composite's
   variance expression, without needing normalized sample weights.
   Exact checked proposition: forall components,
   matrix_quadratic_form (map fst components)
     (covariance_matrix components) =
   variance (linear_combination components).
   Premises and side conditions: Finite component lists and outcome
   lists, with arbitrary real coefficients and sample weights.
   Duplicates are counted. Nonnegative weights and total_mass = 1
   are not required for this identity, but matter for proving
   nonnegativity of the resulting variance or matrix form.
   Proof/definition method: Rewrite through the previously checked
   covariance_matrix_quadratic_form_identity and reuse
   variance_of_general_weighted_sum_unconditional.
   Library reuse: Stdlib.List.map, the generic finite-sum-backed
   covariance matrix identity and unconditional composite variance.
   Boundary: Exact algebra in a finite weighted model, not
   an empirical covariance estimate or a PSD result for signed mass.
   *)
  Theorem covariance_matrix_quadratic_form_is_variance_unconditional :
    forall components,
      matrix_quadratic_form (map fst components)
        (covariance_matrix components) =
      variance (linear_combination components).
  Proof.
    intro components.
    rewrite covariance_matrix_quadratic_form_identity.
    symmetry.
    apply variance_of_general_weighted_sum_unconditional.
  Qed.

  (**
   [covariance_matrix_quadratic_form_is_variance] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Theorem covariance_matrix_quadratic_form_is_variance :
   forall components, total_mass = 1 -> matrix_quadratic_form (map fst components)
   (covariance_matrix components) = variance (linear_combination components).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Apply the stronger
   covariance_matrix_quadratic_form_is_variance_unconditional theorem.
   The original mass normalization hypothesis is deliberately kept
   in the public statement without being used in this derivation.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_matrix_quadratic_form_is_variance :
    forall components,
      total_mass = 1 ->
      matrix_quadratic_form (map fst components)
        (covariance_matrix components) =
      variance (linear_combination components).
  Proof.
    intros components _.
    apply covariance_matrix_quadratic_form_is_variance_unconditional.
  Qed.

  (**
   [covariance_matrix_is_positive_semidefinite] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: The covariance-matrix quadratic form evaluated at
   the coefficients of the given component list is nonnegative:
   it agrees with the variance of their weighted composite.
   Exact checked proposition: Theorem covariance_matrix_is_positive_semidefinite :
   forall components, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) ->
   0 <= matrix_quadratic_form (map fst components) (covariance_matrix components).
   Premises and side conditions: Requires total_mass=1 and nonnegative outcome
   weights on every enumerated sample occurrence. Coefficients
   can be signed and the component list can contain duplicates.
   This particular statement evaluates one supplied coefficient
   vector; related basis lemmas address arbitrary coefficient vectors.
   Proof/definition method: Rewrite the matrix quadratic expression as the
   variance of the weighted score using
   covariance_matrix_quadratic_form_is_variance, then invoke
   variance_nonnegative with the explicit mass hypotheses.
   Library reuse: Stdlib.List.map, FiniteSum, covariance matrix identities,
   covariance_matrix_quadratic_form_is_variance and variance_nonnegative.
   Boundary: Nonnegative real quadratic form for the finite
   sample representation, not an empirical estimated matrix
   certificate or positive definiteness (strictly positive for
   nonzero coefficient vectors).
*)
  Theorem covariance_matrix_is_positive_semidefinite :
    forall components,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <= matrix_quadratic_form (map fst components)
        (covariance_matrix components).
  Proof.
    intros components Hmass Hnonneg.
    rewrite (covariance_matrix_quadratic_form_is_variance
      components Hmass).
    apply variance_nonnegative; assumption.
  Qed.


  (* Elementary variance and correlation bounds derived from positivity,
     rather than assuming any covariance or Pearson coefficient bounds. *)

  (**
   [covariance_at_most_half_sum_of_variances] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_at_most_half_sum_of_variances :
   forall f g, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> 2 *
   covariance f g <= variance f + variance g.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra), ring/field
   normalization; references include variance_nonnegative, variance_extensional,
   variance_of_two_weighted_scores.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_at_most_half_sum_of_variances :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      2 * covariance f g <= variance f + variance g.
  Proof.
    intros f g Hmass Hw.
    pose proof
      (variance_nonnegative (fun x => f x - g x) Hmass Hw) as Hvar.
    assert (Hidentity :
      variance (fun x => f x - g x) =
        variance f + variance g - 2 * covariance f g).
    { transitivity
        (variance (fun x => 1 * f x + (-1) * g x)).
      - apply variance_extensional; intro x; ring.
      - rewrite variance_of_two_weighted_scores; ring. }
    rewrite Hidentity in Hvar.
    lra.
  Qed.

  (**
   [covariance_at_least_negative_half_sum_of_variances] (theorem) — Finite weighted
   score expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   covariance_at_least_negative_half_sum_of_variances : forall f g, total_mass = 1 ->
   (forall x, In x samples -> 0 <= weight x) -> - (variance f + variance g) <= 2 *
   covariance f g.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra); references include
   variance_nonnegative, variance_of_two_score_sum.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_at_least_negative_half_sum_of_variances :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      - (variance f + variance g) <= 2 * covariance f g.
  Proof.
    intros f g Hmass Hw.
    pose proof
      (variance_nonnegative (fun x => f x + g x) Hmass Hw) as Hvar.
    rewrite variance_of_two_score_sum in Hvar.
    lra.
  Qed.

  (**
   [covariance_of_unit_variance_scores_bounded] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_of_unit_variance_scores_bounded :
   forall f g, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) ->
   variance f = 1 -> variance g = 1 -> -1 <= covariance f g /\ covariance f g <= 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership; stated unit-variance conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra); references include
   covariance_at_most_half_sum_of_variances,
   covariance_at_least_negative_half_sum_of_variances.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_of_unit_variance_scores_bounded :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      variance f = 1 ->
      variance g = 1 ->
      -1 <= covariance f g /\ covariance f g <= 1.
  Proof.
    intros f g Hmass Hw Hf Hg.
    pose proof
      (covariance_at_most_half_sum_of_variances f g Hmass Hw)
      as Hupper.
    pose proof
      (covariance_at_least_negative_half_sum_of_variances
        f g Hmass Hw) as Hlower.
    rewrite Hf, Hg in Hupper, Hlower.
    lra.
  Qed.

  (**
   [average_of_two_unit_variance_scores_bounded] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem average_of_two_unit_variance_scores_bounded :
   forall f g, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) ->
   variance f = 1 -> variance g = 1 -> 0 <= variance (fun x => (f x + g x) / 2) /\
   variance (fun x => (f x + g x) / 2) <= 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership; stated unit-variance conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra); references include
   covariance_of_unit_variance_scores_bounded, variance_of_two_unit_variance_average.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem average_of_two_unit_variance_scores_bounded :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      variance f = 1 ->
      variance g = 1 ->
      0 <= variance (fun x => (f x + g x) / 2) /\
      variance (fun x => (f x + g x) / 2) <= 1.
  Proof.
    intros f g Hmass Hw Hf Hg.
    pose proof
      (covariance_of_unit_variance_scores_bounded
        f g Hmass Hw Hf Hg) as [Hlower Hupper].
    rewrite (variance_of_two_unit_variance_average f g Hf Hg).
    split; lra.
  Qed.


  (* For a feasible finite battery, the average correlation cannot be
     arbitrarily negative: the covariance matrix is positive semidefinite.
     This gives rho >= -1/(n-1), without assuming equicorrelation. *)

  (**
   [feasible_average_pair_correlation_lower_bound] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Establishes a correlation, square-root or reliability
   identity under the stated real-number constraints.
   Exact checked proposition: Theorem feasible_average_pair_correlation_lower_bound :
   forall fs n rho, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> n
   = INR (length fs) -> 1 < n -> (forall f, In f fs -> variance f = 1) -> 2 *
   unordered_covariance_sum fs = n * (n - 1) * rho -> -1 / (n - 1) <= rho.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; dimension/length compatibility where required; sample or list
   membership; stated unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra), polynomial real
   arithmetic (Psatz), ring/field normalization; references include
   variance_nonnegative, equal_weight_variance_from_finite_covariances, Hidentity.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem feasible_average_pair_correlation_lower_bound :
    forall fs n rho,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      n = INR (length fs) ->
      1 < n ->
      (forall f, In f fs -> variance f = 1) ->
      2 * unordered_covariance_sum fs = n * (n - 1) * rho ->
      -1 / (n - 1) <= rho.
  Proof.
    intros fs n rho Hmass Hw Hlength Hn Hunit Hpair.
    pose proof (variance_nonnegative
      (fun x => sum_scores fs x / n) Hmass Hw) as Hvariance.
    rewrite (equal_weight_variance_from_finite_covariances
      fs n rho Hmass Hlength Hn Hunit Hpair) in Hvariance.
    assert (Hidentity :
      rho + (1 - rho) / n = (1 + (n - 1) * rho) / n).
    { field; lra. }
    rewrite Hidentity in Hvariance.
    assert (Hnumerator : 0 <= 1 + (n - 1) * rho).
    { unfold Rdiv in Hvariance.
      assert (Hinv : 0 < / n).
      { apply Rinv_0_lt_compat; lra. }
      nra. }
    assert (Hdiff :
      rho - (-1 / (n - 1)) = (1 + (n - 1) * rho) / (n - 1)).
    { field; lra. }
    assert (Hnonneg : 0 <= rho - (-1 / (n - 1))).
    { rewrite Hdiff.
      unfold Rdiv.
      assert (Hinv : 0 < / (n - 1)).
      { apply Rinv_0_lt_compat; lra. }
      nra. }
    lra.
  Qed.


  (**
   [covariance_row_sum_bounded_by_count] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma covariance_row_sum_bounded_by_count : forall f
   fs, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> variance f = 1
   -> (forall g, In g fs -> variance g = 1) -> covariance_row_sum f fs <= INR (length
   fs).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; dimension/length compatibility where required; sample or list
   membership; stated unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, ring/field normalization; references include
   covariance_row_sum., FiniteSum.finite_sum_monotone.,
   covariance_of_unit_variance_scores_bounded.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_row_sum_bounded_by_count :
    forall f fs,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      variance f = 1 ->
      (forall g, In g fs -> variance g = 1) ->
      covariance_row_sum f fs <= INR (length fs).
  Proof.
    intros f fs Hmass Hw Hf Hunit.
    unfold covariance_row_sum.
    replace (INR (length fs)) with
      (FiniteSum.finite_sum (fun _ => 1) fs).
    - apply FiniteSum.finite_sum_monotone.
      intros g Hin.
      pose proof (covariance_of_unit_variance_scores_bounded
        f g Hmass Hw Hf (Hunit g Hin)) as [_ Hcov].
      exact Hcov.
    - rewrite FiniteSum.finite_sum_const; ring.
  Qed.

  (**
   [unordered_covariance_sum_bounded_by_pair_count] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Lemma unordered_covariance_sum_bounded_by_pair_count :
   forall fs, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> (forall
   f, In f fs -> variance f = 1) -> 2 * unordered_covariance_sum fs <= INR (length
   fs) * (INR (length fs) - 1).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; dimension/length compatibility where required; sample or list
   membership; stated unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, reuse of previously established lemmas, linear real arithmetic (Lra),
   polynomial real arithmetic (Psatz), definitional reduction; references include
   S_INR., covariance_row_sum_bounded_by_count.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma unordered_covariance_sum_bounded_by_pair_count :
    forall fs,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall f, In f fs -> variance f = 1) ->
      2 * unordered_covariance_sum fs <=
        INR (length fs) * (INR (length fs) - 1).
  Proof.
    induction fs as [|f rest IH]; intros Hmass Hw Hunit.
    - simpl; lra.
    - cbn [unordered_covariance_sum length].
      rewrite S_INR.
      assert (Hf : variance f = 1).
      { apply Hunit; simpl; auto. }
      assert (Hrest : forall g, In g rest -> variance g = 1).
      { intros g Hg. apply Hunit; simpl; auto. }
      pose proof
        (covariance_row_sum_bounded_by_count f rest
          Hmass Hw Hf Hrest) as Hrow.
      specialize (IH Hmass Hw Hrest).
      nra.
  Qed.

  (**
   [feasible_average_pair_correlation_upper_bound] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Establishes a correlation, square-root or reliability
   identity under the stated real-number constraints.
   Exact checked proposition: Theorem feasible_average_pair_correlation_upper_bound :
   forall fs n rho, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> n
   = INR (length fs) -> 1 < n -> (forall f, In f fs -> variance f = 1) -> 2 *
   unordered_covariance_sum fs = n * (n - 1) * rho -> rho <= 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; dimension/length compatibility where required; sample or list
   membership; stated unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, polynomial real arithmetic (Psatz); references
   include unordered_covariance_sum_bounded_by_pair_count.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem feasible_average_pair_correlation_upper_bound :
    forall fs n rho,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      n = INR (length fs) ->
      1 < n ->
      (forall f, In f fs -> variance f = 1) ->
      2 * unordered_covariance_sum fs = n * (n - 1) * rho ->
      rho <= 1.
  Proof.
    intros fs n rho Hmass Hw Hlength Hn Hunit Hpair.
    pose proof
      (unordered_covariance_sum_bounded_by_pair_count
        fs Hmass Hw Hunit) as Hsum.
    rewrite <- Hlength in Hsum.
    rewrite Hpair in Hsum.
    assert (Hd : 0 < n * (n - 1)) by nra.
    set (d := n * (n - 1)) in *.
    nra.
  Qed.

  (**
   [feasible_average_pair_correlation_interval] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Establishes a correlation, square-root or reliability
   identity under the stated real-number constraints.
   Exact checked proposition: Theorem feasible_average_pair_correlation_interval :
   forall fs n rho, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> n
   = INR (length fs) -> 1 < n -> (forall f, In f fs -> variance f = 1) -> 2 *
   unordered_covariance_sum fs = n * (n - 1) * rho -> -1 / (n - 1) <= rho /\ rho <=
   1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; dimension/length compatibility where required; sample or list
   membership; stated unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include feasible_average_pair_correlation_lower_bound,
   feasible_average_pair_correlation_upper_bound.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem feasible_average_pair_correlation_interval :
    forall fs n rho,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      n = INR (length fs) ->
      1 < n ->
      (forall f, In f fs -> variance f = 1) ->
      2 * unordered_covariance_sum fs = n * (n - 1) * rho ->
      -1 / (n - 1) <= rho /\ rho <= 1.
  Proof.
    intros fs n rho Hmass Hw Hlength Hn Hunit Hpair.
    split.
    - apply (feasible_average_pair_correlation_lower_bound
        fs n rho Hmass Hw Hlength Hn Hunit Hpair).
    - apply (feasible_average_pair_correlation_upper_bound
        fs n rho Hmass Hw Hlength Hn Hunit Hpair).
  Qed.


  (* Cauchy--Schwarz for finite covariance, derived from the nonnegativity
     of every variance Var(f + t*g).  This is stronger than the previously
     established arithmetic-mean bound on two covariance entries. *)

  (**
   [nonnegative_quadratic_discriminant] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma nonnegative_quadratic_discriminant : forall A B
   C, 0 <= A -> 0 <= C -> (forall t, 0 <= A + 2 * t * B + t * t * C) -> B * B <= A *
   C.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, linear real arithmetic (Lra), polynomial
   real arithmetic (Psatz), ring/field normalization; references include
   Rinv_0_lt_compat, HCpos..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma nonnegative_quadratic_discriminant :
    forall A B C,
      0 <= A -> 0 <= C ->
      (forall t, 0 <= A + 2 * t * B + t * t * C) ->
      B * B <= A * C.
  Proof.
    intros A B C HA HC Hquad.
    destruct (Rlt_dec 0 C) as [HCpos | HCnot].
    - specialize (Hquad (- B / C)).
      assert (Hexpr :
        A + 2 * (- B / C) * B +
          (- B / C) * (- B / C) * C =
        (A * C - B * B) / C).
      { field; lra. }
      rewrite Hexpr in Hquad.
      unfold Rdiv in Hquad.
      assert (Hinv : 0 < / C).
      { apply Rinv_0_lt_compat; exact HCpos. }
      nra.
    - assert (Hzero : C = 0) by lra.
      subst C.
      destruct (Req_EM_T B 0) as [HB | HB].
      + subst B; nra.
      + specialize (Hquad (- (A + 1) / (2 * B))).
        assert (Hexpr :
          A + 2 * (- (A + 1) / (2 * B)) * B +
              (- (A + 1) / (2 * B)) *
              (- (A + 1) / (2 * B)) * 0 = -1).
        { field; nra. }
        rewrite Hexpr in Hquad.
        lra.
  Qed.

  (**
   [finite_covariance_cauchy_schwarz_squared] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Establishes the finite probabilistic covariance
   Cauchy-Schwarz bound Cov(f,g)^2 <= Var(f) Var(g), including
   the degenerate case of one or both zero variances.
   Exact checked proposition: Theorem finite_covariance_cauchy_schwarz_squared :
   forall f g, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) ->
   covariance f g * covariance f g <= variance f * variance g.
   Premises and side conditions: The sample mass is normalized to one and each
   enumerated weight is nonnegative; no strict variance
   positivity or score independence is needed. Score values
   and outcomes are otherwise unrestricted real-valued data.
   Proof/definition method: Use nonnegativity of every variance to establish
   positivity of the quadratic variance of f + t*g; expand
   using variance_of_two_score_sum and covariance_scale_second,
   and apply the already proved nonnegative_quadratic_discriminant.
   Library reuse: Stdlib.Reals ring normalization, Lra/Psatz,
   variance_nonnegative, nonnegative_quadratic_discriminant,
   variance_of_two_score_sum and covariance_scale_second.
   Boundary: Squared covariance inequality for a finite
   weighted distribution. The bound alone does not estimate a
   correlation or assert Gaussianity; normalized correlations
   require nonzero standard deviations.
*)
  Theorem finite_covariance_cauchy_schwarz_squared :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      covariance f g * covariance f g <= variance f * variance g.
  Proof.
    intros f g Hmass Hw.
    apply nonnegative_quadratic_discriminant.
    - apply variance_nonnegative; assumption.
    - apply variance_nonnegative; assumption.
    - intro t.
      pose proof (variance_nonnegative
        (fun x => f x + t * g x) Hmass Hw) as Hvar.
      rewrite variance_of_two_score_sum,
        variance_of_scaled_score, covariance_scale_second in Hvar.
      replace (variance f + (t * t) * variance g +
               2 * (t * covariance f g))
        with (variance f + 2 * t * covariance f g +
              t * t * variance g) in Hvar by ring.
      exact Hvar.
  Qed.

  (**
   [zero_variance_implies_zero_covariance_first] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem zero_variance_implies_zero_covariance_first :
   forall f g, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) ->
   variance f = 0 -> covariance f g = 0.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, polynomial real arithmetic (Psatz); references
   include finite_covariance_cauchy_schwarz_squared.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem zero_variance_implies_zero_covariance_first :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      variance f = 0 ->
      covariance f g = 0.
  Proof.
    intros f g Hmass Hw Hzero.
    pose proof
      (finite_covariance_cauchy_schwarz_squared f g Hmass Hw)
      as Hcs.
    rewrite Hzero in Hcs.
    nra.
  Qed.

  (**
   [zero_variance_implies_zero_covariance_second] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem zero_variance_implies_zero_covariance_second :
   forall f g, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) ->
   variance g = 0 -> covariance f g = 0.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include covariance_symmetric.,
   zero_variance_implies_zero_covariance_first.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem zero_variance_implies_zero_covariance_second :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      variance g = 0 ->
      covariance f g = 0.
  Proof.
    intros f g Hmass Hw Hzero.
    rewrite covariance_symmetric.
    apply zero_variance_implies_zero_covariance_first;
      assumption.
  Qed.

  (**
   [nonzero_covariance_implies_positive_variances] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem nonzero_covariance_implies_positive_variances :
   forall f g, total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) ->
   covariance f g <> 0 -> 0 < variance f /\ 0 < variance g.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, reuse of previously
   established lemmas, linear real arithmetic (Lra); references include
   variance_nonnegative, zero_variance_implies_zero_covariance_first,
   zero_variance_implies_zero_covariance_second.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem nonzero_covariance_implies_positive_variances :
    forall f g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      covariance f g <> 0 ->
      0 < variance f /\ 0 < variance g.
  Proof.
    intros f g Hmass Hw Hcov.
    pose proof (variance_nonnegative f Hmass Hw) as Hf.
    pose proof (variance_nonnegative g Hmass Hw) as Hg.
    split.
    - destruct (Rle_dec (variance f) 0) as [Hle | Hnot].
      + assert (Hz : variance f = 0) by lra.
        pose proof
          (zero_variance_implies_zero_covariance_first
            f g Hmass Hw Hz) as Hc.
        contradiction.
      + lra.
    - destruct (Rle_dec (variance g) 0) as [Hle | Hnot].
      + assert (Hz : variance g = 0) by lra.
        pose proof
          (zero_variance_implies_zero_covariance_second
            f g Hmass Hw Hz) as Hc.
        contradiction.
      + lra.
  Qed.


  (* A fixed basis of scores, with the covariance matrix independent of the
     coefficients.  The equal-length premise prevents silent truncation by
     the standard List.combine operation. *)

  (* Reuse List.combine and the general weighted combination; the
     equal-length premise in subsequent theorems avoids truncation. *)
  (**
   [weighted_basis_sum] (definition) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Defines weighted basis sum using explicit Rocq operations,
   so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition weighted_basis_sum (coefficients : list R) (basis :
   list (Outcome -> R)) (x : Outcome) : R := linear_combination (combine coefficients
   basis) x.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition weighted_basis_sum
    (coefficients : list R) (basis : list (Outcome -> R))
    (x : Outcome) : R :=
    linear_combination (combine coefficients basis) x.

  (**
   [basis_covariance_matrix] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines basis covariance matrix using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition basis_covariance_matrix (basis : list (Outcome ->
   R)) : list (list R) := map (fun f => map (fun g => covariance f g) basis) basis.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition basis_covariance_matrix
    (basis : list (Outcome -> R)) : list (list R) :=
    map (fun f => map (fun g => covariance f g) basis) basis.

  (**
   [basis_cross_covariance_matrix] (definition) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Defines basis cross covariance matrix using explicit Rocq
   operations, so later theorems can refer to one stable mathematical object.
   Exact declaration: Definition basis_cross_covariance_matrix (left right : list
   (Outcome -> R)) : list (list R) := map (fun f => map (fun g => covariance f g)
   right) left.
   Premises and side conditions: Only the declared parameters, data fields, and types
   constrain this construction; no extraneous postulates are introduced.
   Proof/definition method: Definitionally uses the shown expression/record
   constructor; proof obligations, if any, are attached to this declaration alone.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Definition basis_cross_covariance_matrix
    (left right : list (Outcome -> R)) : list (list R) :=
    map (fun f => map (fun g => covariance f g) right) left.

  (**
   [weighted_basis_sum_as_combination] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma weighted_basis_sum_as_combination : forall
   coefficients basis x, weighted_basis_sum coefficients basis x = linear_combination
   (combine coefficients basis) x.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, definitional
   reduction.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma weighted_basis_sum_as_combination :
    forall coefficients basis x,
      weighted_basis_sum coefficients basis x =
      linear_combination (combine coefficients basis) x.
  Proof. reflexivity. Qed.

  (* Stdlib.List.combine_split is the authoritative inverse of
     List.combine for equal-length lists. A single projection bridge
     replaces two separate list-length induction proofs below. *)
  (**
   [split_as_projection_maps] (lemma) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Proves a list-structural invariant without custom sorting or
   indexing.
   Exact checked proposition: Lemma split_as_projection_maps : forall (components :
   list (R * (Outcome -> R))), split components = (map fst components, map snd
   components).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses structural induction, rewriting of
   equalities, definitional reduction.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma split_as_projection_maps :
    forall (components : list (R * (Outcome -> R))),
      split components = (map fst components, map snd components).
  Proof.
    induction components as [|[a f] components IH]; simpl.
    - reflexivity.
    - rewrite IH; reflexivity.
  Qed.

  (**
   [coefficients_of_combine] (lemma) — Finite weighted score expectations, variances
   and covariance matrices.
   Mathematical meaning: Proves a list-structural invariant without custom sorting or
   indexing.
   Exact checked proposition: Lemma coefficients_of_combine : forall (coefficients :
   list R) (basis : list (Outcome -> R)), length coefficients = length basis -> map
   fst (combine coefficients basis) = coefficients.
   Premises and side conditions: The displayed hypotheses include dimension/length
   compatibility where required. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include combine_split,
   split_as_projection_maps, f_equal.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma coefficients_of_combine :
    forall (coefficients : list R) (basis : list (Outcome -> R)),
      length coefficients = length basis ->
      map fst (combine coefficients basis) = coefficients.
  Proof.
    intros coefficients basis Hlength.
    pose proof (combine_split coefficients basis Hlength) as Hsplit.
    rewrite split_as_projection_maps in Hsplit.
    exact (f_equal fst Hsplit).
  Qed.

  (**
   [basis_of_combine] (lemma) — Finite weighted score expectations, variances and
   covariance matrices.
   Mathematical meaning: Proves a list-structural invariant without custom sorting or
   indexing.
   Exact checked proposition: Lemma basis_of_combine : forall (coefficients : list R)
   (basis : list (Outcome -> R)), length coefficients = length basis -> map snd
   (combine coefficients basis) = basis.
   Premises and side conditions: The displayed hypotheses include dimension/length
   compatibility where required. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include combine_split,
   split_as_projection_maps, f_equal.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma basis_of_combine :
    forall (coefficients : list R) (basis : list (Outcome -> R)),
      length coefficients = length basis ->
      map snd (combine coefficients basis) = basis.
  Proof.
    intros coefficients basis Hlength.
    pose proof (combine_split coefficients basis Hlength) as Hsplit.
    rewrite split_as_projection_maps in Hsplit.
    exact (f_equal snd Hsplit).
  Qed.

  (**
   [covariance_matrix_uses_only_basis] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma covariance_matrix_uses_only_basis : forall
   components, covariance_matrix components = basis_covariance_matrix (map snd
   components).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, definitional reduction; references include
   covariance_matrix, map_map., map_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_matrix_uses_only_basis :
    forall components,
      covariance_matrix components =
        basis_covariance_matrix (map snd components).
  Proof.
    intros components.
    unfold covariance_matrix, covariance_cross_matrix,
      basis_covariance_matrix.
    rewrite map_map.
    apply map_ext; intro component.
    rewrite map_map.
    reflexivity.
  Qed.

  (**
   [covariance_cross_matrix_uses_only_bases] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma covariance_cross_matrix_uses_only_bases : forall
   left right, covariance_cross_matrix left right = basis_cross_covariance_matrix
   (map snd left) (map snd right).
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, definitional reduction; references include
   covariance_cross_matrix, map_map., map_ext.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma covariance_cross_matrix_uses_only_bases :
    forall left right,
      covariance_cross_matrix left right =
        basis_cross_covariance_matrix
          (map snd left) (map snd right).
  Proof.
    intros left right.
    unfold covariance_cross_matrix, basis_cross_covariance_matrix.
    rewrite map_map.
    apply map_ext; intro component.
    rewrite map_map.
    reflexivity.
  Qed.

  (**
   [fixed_basis_covariance_matrix_representation] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Theorem fixed_basis_covariance_matrix_representation :
   forall coefficients basis, length coefficients = length basis -> covariance_matrix
   (combine coefficients basis) = basis_covariance_matrix basis.
   Premises and side conditions: The displayed hypotheses include dimension/length
   compatibility where required. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, definitional
   reduction; references include covariance_matrix_uses_only_basis.,
   basis_of_combine.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem fixed_basis_covariance_matrix_representation :
    forall coefficients basis,
      length coefficients = length basis ->
      covariance_matrix (combine coefficients basis) =
        basis_covariance_matrix basis.
  Proof.
    intros coefficients basis Hlength.
    rewrite covariance_matrix_uses_only_basis.
    rewrite (basis_of_combine coefficients basis Hlength).
    reflexivity.
  Qed.

  (**
   [fixed_basis_weighted_variance_identity] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem fixed_basis_weighted_variance_identity : forall
   coefficients basis, length coefficients = length basis -> total_mass = 1 ->
   variance (weighted_basis_sum coefficients basis) = matrix_quadratic_form
   coefficients (basis_covariance_matrix basis).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; dimension/length compatibility where required. No further assumptions are
   implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include variance_extensional,
   weighted_basis_sum_as_combination., covariance_matrix_quadratic_form_is_variance.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem fixed_basis_weighted_variance_identity :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      variance (weighted_basis_sum coefficients basis) =
        matrix_quadratic_form coefficients
          (basis_covariance_matrix basis).
  Proof.
    intros coefficients basis Hlength Hmass.
    transitivity
      (variance (linear_combination
        (combine coefficients basis))).
    - apply variance_extensional; intro x.
      apply weighted_basis_sum_as_combination.
    - symmetry.
      pose proof
        (covariance_matrix_quadratic_form_is_variance
          (combine coefficients basis) Hmass) as Hidentity.
      rewrite (coefficients_of_combine
        coefficients basis Hlength) in Hidentity.
      rewrite (fixed_basis_covariance_matrix_representation
        coefficients basis Hlength) in Hidentity.
      exact Hidentity.
  Qed.

  (**
   [fixed_basis_covariance_matrix_positive_semidefinite] (theorem) — Finite weighted
   score expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Theorem
   fixed_basis_covariance_matrix_positive_semidefinite : forall basis coefficients,
   length coefficients = length basis -> total_mass = 1 -> (forall x, In x samples ->
   0 <= weight x) -> 0 <= matrix_quadratic_form coefficients (basis_covariance_matrix
   basis).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; dimension/length compatibility where required; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include variance_nonnegative.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem fixed_basis_covariance_matrix_positive_semidefinite :
    forall basis coefficients,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <= matrix_quadratic_form coefficients
        (basis_covariance_matrix basis).
  Proof.
    intros basis coefficients Hlength Hmass Hw.
    rewrite <-
      (fixed_basis_weighted_variance_identity
        coefficients basis Hlength Hmass).
    apply variance_nonnegative; assumption.
  Qed.


  (* Correlation bounds for scores whose positive standard deviations are
     provided with the proof that each squares to its finite variance. *)

  (**
   [normalized_covariance_is_between_minus_one_and_one] (theorem) — Finite weighted
   score expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   normalized_covariance_is_between_minus_one_and_one : forall f g sd_f sd_g,
   total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> 0 < sd_f -> 0 <
   sd_g -> variance f = sd_f * sd_f -> variance g = sd_g * sd_g -> -1 <= covariance f
   g / (sd_f * sd_g) /\ covariance f g / (sd_f * sd_g) <= 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership; stated unit-variance conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, linear real arithmetic (Lra), polynomial
   real arithmetic (Psatz), ring/field normalization; references include
   finite_covariance_cauchy_schwarz_squared, Rinv_0_lt_compat.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem normalized_covariance_is_between_minus_one_and_one :
    forall f g sd_f sd_g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 < sd_f -> 0 < sd_g ->
      variance f = sd_f * sd_f ->
      variance g = sd_g * sd_g ->
      -1 <= covariance f g / (sd_f * sd_g) /\
            covariance f g / (sd_f * sd_g) <= 1.
  Proof.
    intros f g sd_f sd_g Hmass Hw Hsf Hsg Hvarf Hvarg.
    pose proof (finite_covariance_cauchy_schwarz_squared
      f g Hmass Hw) as Hcs.
    rewrite Hvarf, Hvarg in Hcs.
    replace ((sd_f * sd_f) * (sd_g * sd_g))
      with ((sd_f * sd_g) * (sd_f * sd_g)) in Hcs by ring.
    assert (Hden : 0 < sd_f * sd_g) by nra.
    assert (Hbound :
      - (sd_f * sd_g) <= covariance f g /\
      covariance f g <= sd_f * sd_g) by nra.
    assert (Hinv : 0 < / (sd_f * sd_g)).
    { apply Rinv_0_lt_compat; exact Hden. }
    assert (Hid : (sd_f * sd_g) * / (sd_f * sd_g) = 1).
    { field; lra. }
    unfold Rdiv.
    destruct Hbound as [Hlow Hhigh].
    split; nra.
  Qed.

  (**
   [centered_standardized_covariance_in_unit_interval] (theorem) — Finite weighted
   score expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   centered_standardized_covariance_in_unit_interval : forall f g sd_f sd_g,
   total_mass = 1 -> (forall x, In x samples -> 0 <= weight x) -> 0 < sd_f -> 0 <
   sd_g -> variance f = sd_f * sd_f -> variance g = sd_g * sd_g -> -1 <= covariance
   (fun x => (f x - expect f) / sd_f) (fun x => (g x - expect g) / sd_g) /\
   covariance (fun x => (f x - expect f) / sd_f) (fun x => (g x - expect g) / sd_g)
   <= 1.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership; stated unit-variance conditions. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra); references include
   covariance_of_centered_standardized_scores,
   normalized_covariance_is_between_minus_one_and_one.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem centered_standardized_covariance_in_unit_interval :
    forall f g sd_f sd_g,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 < sd_f -> 0 < sd_g ->
      variance f = sd_f * sd_f ->
      variance g = sd_g * sd_g ->
      -1 <= covariance
        (fun x => (f x - expect f) / sd_f)
        (fun x => (g x - expect g) / sd_g) /\
      covariance
        (fun x => (f x - expect f) / sd_f)
        (fun x => (g x - expect g) / sd_g) <= 1.
  Proof.
    intros f g sd_f sd_g Hmass Hw Hsf Hsg Hvarf Hvarg.
    assert (Hnzf : sd_f <> 0) by lra.
    assert (Hnzg : sd_g <> 0) by lra.
    rewrite (covariance_of_centered_standardized_scores
      f g sd_f sd_g Hmass Hnzf Hnzg).
    apply normalized_covariance_is_between_minus_one_and_one;
      assumption.
  Qed.

  (**
   [unit_covariance_one_iff_difference_has_zero_variance] (theorem) — Finite weighted
   score expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   unit_covariance_one_iff_difference_has_zero_variance : forall f g, variance f = 1
   -> variance g = 1 -> covariance f g = 1 <-> variance (fun x => f x - g x) = 0.
   Premises and side conditions: The displayed hypotheses include stated
   unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, linear real arithmetic (Lra), ring/field
   normalization; references include variance_extensional,
   variance_of_two_weighted_scores, Hidentity..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem unit_covariance_one_iff_difference_has_zero_variance :
    forall f g,
      variance f = 1 -> variance g = 1 ->
      covariance f g = 1 <->
      variance (fun x => f x - g x) = 0.
  Proof.
    intros f g Hf Hg.
    assert (Hidentity :
      variance (fun x => f x - g x) =
      2 - 2 * covariance f g).
    { transitivity
        (variance (fun x => 1 * f x + (-1) * g x)).
      - apply variance_extensional; intro x; ring.
      - rewrite variance_of_two_weighted_scores, Hf, Hg; ring. }
    rewrite Hidentity.
    split; intro H; lra.
  Qed.

  (**
   [unit_covariance_minus_one_iff_sum_has_zero_variance] (theorem) — Finite weighted
   score expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   unit_covariance_minus_one_iff_sum_has_zero_variance : forall f g, variance f = 1
   -> variance g = 1 -> covariance f g = -1 <-> variance (fun x => f x + g x) = 0.
   Premises and side conditions: The displayed hypotheses include stated
   unit-variance conditions. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, linear real
   arithmetic (Lra); references include variance_of_two_score_sum.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem unit_covariance_minus_one_iff_sum_has_zero_variance :
    forall f g,
      variance f = 1 -> variance g = 1 ->
      covariance f g = -1 <->
      variance (fun x => f x + g x) = 0.
  Proof.
    intros f g Hf Hg.
    rewrite variance_of_two_score_sum, Hf, Hg.
    split; intro H; lra.
  Qed.


  (* Reuse the already proved shift invariance and covariance bilinearity
     rather than expanding finite expectations again. *)

  (**
   [variance_of_affine_score] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_affine_score : forall f a b,
   total_mass = 1 -> variance (fun x => a * f x + b) = (a * a) * variance f.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include variance_of_shifted_score,
   variance_of_scaled_score..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_affine_score :
    forall f a b,
      total_mass = 1 ->
      variance (fun x => a * f x + b) =
        (a * a) * variance f.
  Proof.
    intros f a b Hmass.
    rewrite (variance_of_shifted_score
      (fun x => a * f x) b Hmass).
    apply variance_of_scaled_score.
  Qed.

  (**
   [covariance_of_affine_scores] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem covariance_of_affine_scores : forall f g a b c
   d, total_mass = 1 -> covariance (fun x => a * f x + b) (fun x => c * g x + d) = a
   * c * covariance f g.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, ring/field
   normalization; references include covariance_invariant_under_first_shift,
   covariance_invariant_under_second_shift, covariance_scale_first.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem covariance_of_affine_scores :
    forall f g a b c d,
      total_mass = 1 ->
      covariance (fun x => a * f x + b)
                 (fun x => c * g x + d) =
        a * c * covariance f g.
  Proof.
    intros f g a b c d Hmass.
    rewrite (covariance_invariant_under_first_shift
      (fun x => a * f x) (fun x => c * g x + d) b Hmass).
    rewrite (covariance_invariant_under_second_shift
      (fun x => a * f x) (fun x => c * g x) d Hmass).
    rewrite covariance_scale_first, covariance_scale_second.
    ring.
  Qed.

  (* Matrix dimensions are consequences of Stdlib.List.length_map and
     in_map_iff, rather than new recursive matrix-size functions. *)

  (**
   [basis_covariance_matrix_row_count] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma basis_covariance_matrix_row_count : forall basis,
   length (basis_covariance_matrix basis) = length basis.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include basis_covariance_matrix., length_map..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma basis_covariance_matrix_row_count :
    forall basis,
      length (basis_covariance_matrix basis) = length basis.
  Proof.
    intro basis.
    unfold basis_covariance_matrix.
    apply length_map.
  Qed.

  (**
   [basis_covariance_matrix_column_count] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma basis_covariance_matrix_column_count : forall
   basis row, In row (basis_covariance_matrix basis) -> length row = length basis.
   Premises and side conditions: The displayed hypotheses include dimension/length
   compatibility where required; sample or list membership. No further assumptions
   are implicit.
   Proof/definition method: Kernel proof uses case analysis, reuse of previously
   established lemmas; references include basis_covariance_matrix, in_map_iff,
   length_map..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma basis_covariance_matrix_column_count :
    forall basis row,
      In row (basis_covariance_matrix basis) ->
      length row = length basis.
  Proof.
    intros basis row Hin.
    unfold basis_covariance_matrix in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [f [Hrow _]].
    subst row.
    apply length_map.
  Qed.

  (**
   [basis_cross_covariance_matrix_row_count] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma basis_cross_covariance_matrix_row_count : forall
   left right, length (basis_cross_covariance_matrix left right) = length left.
   Premises and side conditions: All required premises are written in the signature.
   No independence or distributional assumption is silently supplied.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include basis_cross_covariance_matrix., length_map..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma basis_cross_covariance_matrix_row_count :
    forall left right,
      length (basis_cross_covariance_matrix left right) =
        length left.
  Proof.
    intros left right.
    unfold basis_cross_covariance_matrix.
    apply length_map.
  Qed.

  (**
   [basis_cross_covariance_matrix_column_count] (lemma) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Connects score covariances with a finite matrix, vector, or
   quadratic-form expression.
   Exact checked proposition: Lemma basis_cross_covariance_matrix_column_count :
   forall left right row, In row (basis_cross_covariance_matrix left right) -> length
   row = length right.
   Premises and side conditions: The displayed hypotheses include dimension/length
   compatibility where required; sample or list membership. No further assumptions
   are implicit.
   Proof/definition method: Kernel proof uses case analysis, reuse of previously
   established lemmas; references include basis_cross_covariance_matrix, in_map_iff,
   length_map..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma basis_cross_covariance_matrix_column_count :
    forall left right row,
      In row (basis_cross_covariance_matrix left right) ->
      length row = length right.
  Proof.
    intros left right row Hin.
    unfold basis_cross_covariance_matrix in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [f [Hrow _]].
    subst row.
    apply length_map.
  Qed.


  (* Reuse the generic nonnegative-zero characterization from
     FiniteSum. Keep the public theorem statement unchanged so existing
     covariance null-direction proofs remain compatible. *)

  (**
   [sum_finite_zero_implies_zero_terms] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma sum_finite_zero_implies_zero_terms : forall xs h,
   (forall x, In x xs -> 0 <= h x) -> sum_finite h xs = 0 -> forall x, In x xs -> h x
   = 0.
   Premises and side conditions: The displayed hypotheses include explicit nonzero or
   strict-positive numerical conditions; sample or list membership. No further
   assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_nonnegative_zero.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma sum_finite_zero_implies_zero_terms :
    forall xs h,
      (forall x, In x xs -> 0 <= h x) ->
      sum_finite h xs = 0 ->
      forall x, In x xs -> h x = 0.
  Proof.
    intros xs h Hnonnegative Hsum x Hin.
    exact (FiniteSum.finite_sum_nonnegative_zero
      xs h Hnonnegative Hsum x Hin).
  Qed.

  (**
   [zero_variance_is_constant_on_positive_mass] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem zero_variance_is_constant_on_positive_mass :
   forall f x, total_mass = 1 -> (forall y, In y samples -> 0 <= weight y) ->
   variance f = 0 -> In x samples -> 0 < weight x -> f x = expect f.
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; sample or list membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses case analysis, rewriting of equalities,
   reuse of previously established lemmas, linear real arithmetic (Lra); references
   include centered_second_moment_identity, Rmult_le_pos., Rle_0_sqr..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem zero_variance_is_constant_on_positive_mass :
    forall f x,
      total_mass = 1 ->
      (forall y, In y samples -> 0 <= weight y) ->
      variance f = 0 ->
      In x samples -> 0 < weight x ->
      f x = expect f.
  Proof.
    intros f x Hmass Hw Hzero Hin Hpositive.
    pose proof (centered_second_moment_identity f Hmass) as Hmom.
    change
      (sum_finite
        (fun y => weight y *
           ((f y - expect f) * (f y - expect f)))
         samples = variance f) in Hmom.
    rewrite Hzero in Hmom.
    assert (Hnonnegative : forall y, In y samples ->
      0 <= weight y * ((f y - expect f) * (f y - expect f))).
    { intros y Hy.
      apply Rmult_le_pos.
      - apply Hw; exact Hy.
      - change (0 <= Rsqr (f y - expect f)).
        apply Rle_0_sqr. }
    pose proof
      (sum_finite_zero_implies_zero_terms
         samples
         (fun y => weight y *
           ((f y - expect f) * (f y - expect f)))
         Hnonnegative Hmom x Hin) as Hterm.
    apply Rmult_integral in Hterm.
    destruct Hterm as [Hweight0 | Hsquare0].
    - lra.
    - apply Rmult_integral in Hsquare0.
      destruct Hsquare0 as [Hcenter0 | Hcenter0]; lra.
  Qed.

  (**
   [null_covariance_direction_constant_on_positive_mass] (theorem) — Finite weighted
   score expectations, variances and covariance matrices.
   Mathematical meaning: Derives a covariance identity or inequality from finite
   weighted expectations.
   Exact checked proposition: Theorem
   null_covariance_direction_constant_on_positive_mass : forall coefficients basis x,
   length coefficients = length basis -> total_mass = 1 -> (forall y, In y samples ->
   0 <= weight y) -> In x samples -> 0 < weight x -> matrix_quadratic_form
   coefficients (basis_covariance_matrix basis) = 0 -> weighted_basis_sum
   coefficients basis x = expect (weighted_basis_sum coefficients basis).
   Premises and side conditions: The displayed hypotheses include unit total sample
   mass; nonnegative outcome weights; explicit nonzero or strict-positive numerical
   conditions; dimension/length compatibility where required; sample or list
   membership. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas; references include
   zero_variance_is_constant_on_positive_mass,
   fixed_basis_weighted_variance_identity, Hquadratic..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem null_covariance_direction_constant_on_positive_mass :
    forall coefficients basis x,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall y, In y samples -> 0 <= weight y) ->
      In x samples -> 0 < weight x ->
      matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 ->
      weighted_basis_sum coefficients basis x =
        expect (weighted_basis_sum coefficients basis).
  Proof.
    intros coefficients basis x Hlength Hmass Hw Hin Hpositive Hquadratic.
    apply zero_variance_is_constant_on_positive_mass;
      try assumption.
    rewrite (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    exact Hquadratic.
  Qed.


  (* The sum of a finite score battery is order independent.
     Stdlib.Sorting.Permutation supplies the list-permutation relation
     and its standard induction; the proof uses only commutativity of
     real addition, not a custom sorting or indexing implementation. *)

  (**
   [sum_scores_permutation_invariant] (lemma) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Derives a sum or expectation identity for the explicitly
   enumerated terms.
   Exact checked proposition: Lemma sum_scores_permutation_invariant : forall fs gs,
   Permutation fs gs -> forall x, sum_scores fs x = sum_scores gs x.
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include FiniteSum.finite_sum_permutation, Hperm..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Lemma sum_scores_permutation_invariant :
    forall fs gs,
      Permutation fs gs ->
      forall x, sum_scores fs x = sum_scores gs x.
  Proof.
    intros fs gs Hperm x.
    change (FiniteSum.finite_sum (fun f => f x) fs =
            FiniteSum.finite_sum (fun f => f x) gs).
    apply FiniteSum.finite_sum_permutation; exact Hperm.
  Qed.

  (**
   [variance_of_permuted_score_sum] (theorem) — Finite weighted score expectations,
   variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem variance_of_permuted_score_sum : forall fs gs,
   Permutation fs gs -> variance (sum_scores fs) = variance (sum_scores gs).
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses reuse of previously established lemmas;
   references include variance_extensional, sum_scores_permutation_invariant, Hperm..
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem variance_of_permuted_score_sum :
    forall fs gs,
      Permutation fs gs ->
      variance (sum_scores fs) = variance (sum_scores gs).
  Proof.
    intros fs gs Hperm.
    apply variance_extensional; intro x.
    apply sum_scores_permutation_invariant; exact Hperm.
  Qed.

  (**
   [equal_weight_variance_permutation_invariant] (theorem) — Finite weighted score
   expectations, variances and covariance matrices.
   Mathematical meaning: Identifies the precise variance, scaling behavior, or
   variance bound for the stated score construction.
   Exact checked proposition: Theorem equal_weight_variance_permutation_invariant :
   forall fs gs n, Permutation fs gs -> variance (fun x => sum_scores fs x / n) =
   variance (fun x => sum_scores gs x / n).
   Premises and side conditions: The displayed hypotheses include Stdlib permutation
   relation. No further assumptions are implicit.
   Proof/definition method: Kernel proof uses rewriting of equalities, reuse of
   previously established lemmas, definitional reduction; references include
   variance_extensional, sum_scores_permutation_invariant.
   Library reuse: Stdlib.List, Sorting.Permutation, Reals and FiniteSum.
   Boundary: Exact finite outcome weights and list score bases, not continuous random
   variables or empirical IQ covariance.
   *)
  Theorem equal_weight_variance_permutation_invariant :
    forall fs gs n,
      Permutation fs gs ->
      variance (fun x => sum_scores fs x / n) =
        variance (fun x => sum_scores gs x / n).
  Proof.
    intros fs gs n Hperm.
    apply variance_extensional; intro x.
    rewrite (sum_scores_permutation_invariant fs gs Hperm x).
    reflexivity.
  Qed.

  (**
   [fixed_basis_covariance_cauchy_schwarz_squared] (theorem) — Finite covariance matrix null-direction analysis.
   Mathematical meaning: Any weighted combination of a finite score basis obeys the Cauchy–Schwarz covariance bound with an arbitrary comparison score, where the first variance is expressed as a covariance-matrix quadratic form.
   Exact checked proposition: For all coefficients basis g, matching coefficient and basis lengths, normalized mass and nonnegative sample weights imply covariance(weighted_basis_sum coefficients basis,g)^2 <= matrix_quadratic_form(coefficients,basis_covariance_matrix basis)*variance(g).
   Premises and side conditions: Length equality makes the fixed-basis matrix representation valid. Weights must be nonnegative on sampled outcomes and total mass must equal one; the comparison score g need not be part of the basis.
   Proof/definition method: Rewrite the quadratic form into the proven variance of the corresponding weighted basis sum and apply the existing finite Cauchy–Schwarz squared theorem, with no new matrix multiplication or finite-sum induction.
   Library reuse: fixed_basis_weighted_variance_identity, finite_covariance_cauchy_schwarz_squared, Stdlib.Reals.
   Boundary: Finite-list covariance matrices only; this is not a spectral rank computation or an empirical correlation bound.
   *)
  Theorem fixed_basis_covariance_cauchy_schwarz_squared :
    forall coefficients basis g,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      covariance (weighted_basis_sum coefficients basis) g *
        covariance (weighted_basis_sum coefficients basis) g <=
      matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) * variance g.
  Proof.
    intros coefficients basis g Hlength Hmass Hw.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply finite_covariance_cauchy_schwarz_squared; assumption.
  Qed.

  (**
   [null_covariance_direction_orthogonal_to_every_score] (theorem) — Finite covariance matrix null-direction analysis.
   Mathematical meaning: If a coefficient vector has zero quadratic form in the finite basis covariance matrix, then its associated weighted score sum has zero covariance with every comparison score, including scores outside the basis.
   Exact checked proposition: For all coefficients basis g, matching lengths, normalized nonnegative sampled weights and a zero basis-covariance quadratic form imply covariance(weighted_basis_sum coefficients basis,g) = 0.
   Premises and side conditions: The matrix-vector dimensions must match; total mass is one and every sampled outcome weight is nonnegative. The zero-quadratic-form premise is exact, not a numerical near-zero tolerance.
   Proof/definition method: Reuse the fixed-basis variance identity to convert zero quadratic form into zero variance, then invoke the previously checked zero_variance_implies_zero_covariance_first theorem.
   Library reuse: fixed_basis_weighted_variance_identity, zero_variance_implies_zero_covariance_first, FiniteSum and Stdlib.Reals.
   Boundary: This is an exact null-direction orthogonality result in the finite covariance model; it does not compute matrix rank or assert positive definiteness.
   *)
  Theorem null_covariance_direction_orthogonal_to_every_score :
    forall coefficients basis g,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 ->
      covariance (weighted_basis_sum coefficients basis) g = 0.
  Proof.
    intros coefficients basis g Hlength Hmass Hw Hquadratic.
    apply zero_variance_implies_zero_covariance_first;
      [exact Hmass|exact Hw|].
    rewrite (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    exact Hquadratic.
  Qed.

  (**
   [null_covariance_direction_pairwise_constant_on_positive_mass] (theorem) — Finite covariance matrix null-direction analysis.
   Mathematical meaning: A zero quadratic-form coefficient direction produces identical weighted-score totals at any two enumerated outcomes having strictly positive mass; both values are the same verified finite expectation.
   Exact checked proposition: For all coefficients basis x y, equal coefficient and basis lengths, normalized nonnegative sampled weights, positive weights at two listed outcomes, and zero quadratic form entail weighted_basis_sum coefficients basis x = weighted_basis_sum coefficients basis y.
   Premises and side conditions: Both x and y must occur in samples with strictly positive individual weights. Zero-weight outcomes are excluded; no assumptions about the distinctness of x and y or statistical independence are made.
   Proof/definition method: Apply the established null_covariance_direction_constant_on_positive_mass theorem separately to both outcomes and use the transitivity of real equality; no new covariance or matrix algebra is implemented.
   Library reuse: null_covariance_direction_constant_on_positive_mass, Stdlib.List.In and real equality transitivity.
   Boundary: This is a finite positive-support consequence of matrix nullity, not a certified general rank-nullity formula or an identification of empirical dimensions.
   *)
  Theorem null_covariance_direction_pairwise_constant_on_positive_mass :
    forall coefficients basis x y,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall z, In z samples -> 0 <= weight z) ->
      In x samples -> 0 < weight x ->
      In y samples -> 0 < weight y ->
      matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 ->
      weighted_basis_sum coefficients basis x =
        weighted_basis_sum coefficients basis y.
  Proof.
    intros coefficients basis x y Hlength Hmass Hw Hinx Hposx
      Hiny Hposy Hquadratic.
    transitivity (expect (weighted_basis_sum coefficients basis)).
    - apply null_covariance_direction_constant_on_positive_mass;
        assumption.
    - symmetry.
      apply null_covariance_direction_constant_on_positive_mass;
        assumption.
  Qed.

  (**
   [variance_of_constant_score_zero] (theorem) — Finite score variance and covariance-matrix degeneracy.
   Mathematical meaning: Any constant-valued score has zero finite variance when the sample weights sum to one; this helper exposes a reusable property instead of repeating the covariance-with-constant proof in matrix examples.
   Exact checked proposition: For every real constant c, total_mass = 1 implies variance (fun _ => c) = 0.
   Premises and side conditions: The only assumption is unit total sample mass; individual nonnegative weights are not required for the exact algebraic identity. The constant may be any real number and the sample may contain repeated outcomes.
   Proof/definition method: Unfold variance as self-covariance and directly apply the already verified covariance_with_constant_first identity under the unit-mass hypothesis.
   Library reuse: covariance_with_constant_first, FiniteMoments.variance, Stdlib.Reals and the shared FiniteSum model.
   Boundary: This is an exact constant-score variance identity for finite weighted outcomes, not a statistical assertion about continuous or observed scores.
   *)
  Theorem variance_of_constant_score_zero :
    forall c,
      total_mass = 1 ->
      variance (fun _ => c) = 0.
  Proof.
    intros c Hmass.
    unfold variance.
    apply covariance_with_constant_first; exact Hmass.
  Qed.

  (**
   [affine_dependent_pair_nontrivial_null_on_samples] (theorem) — Affine-dependent finite covariance directions.
   Mathematical meaning: An exact affine relationship f=a*g+c on each enumerated outcome gives the two-score covariance matrix a nonzero quadratic-null direction [1;-a], even when some weights are negative.
   Exact checked proposition: For all f g a c with total_mass=1 and f x=a*g x+c whenever In x samples, [1;-a]<>[0;0] and matrix_quadratic_form [1;-a] (basis_covariance_matrix [f;g])=0.
   Premises and side conditions: Unit total sample mass and the affine relation on every listed outcome are required. Signed weights, repeated outcomes and zero-weight observations are permitted; no independence condition is assumed.
   Proof/definition method: Prove nonzero coefficients by inversion/Lra. Rewrite the quadratic form via fixed_basis_weighted_variance_identity; transfer the composite-score variance to constant c via variance_extensional_on_samples; simplify Stdlib.List.combine and the existing FiniteSum fold, rewrite the affine equality and use ring, then use variance_of_constant_score_zero.
   Library reuse: fixed_basis_weighted_variance_identity, variance_extensional_on_samples, variance_of_constant_score_zero, Stdlib.List.combine, FiniteSum.finite_sum, ring and Lra.
   Boundary: An exact finite two-score quadratic null witness, not a full covariance-rank algorithm or empirical factor identification.
   *)
  Theorem affine_dependent_pair_nontrivial_null_on_samples :
    forall f g a c,
      total_mass = 1 ->
      (forall x, In x samples -> f x = a * g x + c) ->
      [1; -a] <> ([0; 0] : list R) /\
      matrix_quadratic_form [1; -a]
        (basis_covariance_matrix [f; g]) = 0.
  Proof.
    intros f g a c Hmass Haffine.
    split.
    - intro Hzero.
      inversion Hzero; lra.
    - rewrite <- (fixed_basis_weighted_variance_identity
        [1; -a] [f; g] eq_refl Hmass).
      transitivity (variance (fun _ => c)).
      + apply variance_extensional_on_samples.
        intros x Hx.
        unfold weighted_basis_sum, linear_combination,
          FiniteSum.finite_sum.
        simpl.
        rewrite (Haffine x Hx).
        ring.
      + apply variance_of_constant_score_zero; exact Hmass.
  Qed.

  (**
   [duplicate_basis_nontrivial_null_direction] (theorem) — Finite score variance and covariance-matrix degeneracy.
   Mathematical meaning: A covariance matrix formed from two identical basis scores has a genuinely nonzero coefficient vector [1,-1] whose quadratic form is zero: subtracting the same score from itself yields the constant zero score.
   Exact checked proposition: For all finite real-valued scores f with total_mass=1, [1;-1] differs from the zero coefficient vector [0;0], and matrix_quadratic_form [1;-1] (basis_covariance_matrix [f;f]) = 0.
   Premises and side conditions: Only the unit total-mass hypothesis is needed to use the already-verified fixed-basis weighted variance theorem. The duplicate score functions are exactly identical; no empirical equal-correlation or near-equality assumption is made.
   Proof/definition method: Apply the more general affine_dependent_pair_nontrivial_null_on_samples theorem to the repeated score with slope 1 and offset 0. The score relation follows by ring, removing duplicated fixed-basis variance and list-sum reasoning.
   Library reuse: affine_dependent_pair_nontrivial_null_on_samples and Stdlib.Reals.ring.
   Boundary: This is an explicit finite two-dimensional singularity witness. It does not calculate arbitrary matrix rank, prove the converse rank-nullity theorem, or infer any IQ-test covariance structure.
   *)
  Theorem duplicate_basis_nontrivial_null_direction :
    forall f,
      total_mass = 1 ->
      [1; -1] <> ([0; 0] : list R) /\
      matrix_quadratic_form [1; -1]
        (basis_covariance_matrix [f; f]) = 0.
  Proof.
    intros f Hmass.
    apply (affine_dependent_pair_nontrivial_null_on_samples
      f f 1 0 Hmass).
    intros x _; ring.
  Qed.

  (**
   [expectation_extensional_on_positive_weight_support] (theorem) — Nonnegative weighted finite support and covariance nullity.
   Mathematical meaning: For nonnegative sampled weights, changing a real-valued score on a zero-weight outcome cannot affect its weighted expectation. Agreement is only required on the positive-weight portion of the finite list.
   Exact checked proposition: For all f g, nonnegative sampled weights and f x = g x at all enumerated x with 0 < weight x imply expect f = expect g.
   Premises and side conditions: The weight function must be nonnegative on every listed outcome. The total finite mass may be unnormalized; repeated list occurrences remain counted and zero-weight samples contribute zero even when their score values differ.
   Proof/definition method: Unfold the existing expected-value and FiniteSum aliases, invoke the previously proved finite_sum_ext_in extensionality, and split into zero-weight and positive-weight cases using the standard real-order decision lemma Rle_lt_dec.
   Library reuse: FiniteSum.finite_sum_ext_in, Stdlib.List.map_ext_in, Stdlib.Reals.Rle_lt_dec, Stdlib.Lra, existing expect and sum_finite definitions.
   Boundary: Equality is only on positive-weight listed support; no abstract null-set, continuous measure, or independence hypothesis is introduced.
   *)
  Theorem expectation_extensional_on_positive_weight_support :
    forall f g,
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x -> f x = g x) ->
      expect f = expect g.
  Proof.
    intros f g Hw Hfg.
    unfold expect, sum_finite.
    apply FiniteSum.finite_sum_ext_in.
    intros x Hx.
    destruct (Rle_lt_dec (weight x) 0) as [Hnonpos|Hpositive].
    - assert (Hzero : weight x = 0).
      { pose proof (Hw x Hx); lra. }
      rewrite Hzero; ring.
    - rewrite (Hfg x Hx Hpositive).
      reflexivity.
  Qed.

  (**
   [covariance_extensional_on_positive_weight_support] (theorem) — Nonnegative weighted finite support and covariance nullity.
   Mathematical meaning: For a nonnegative weighted sample, the two marginal expectations and their product expectation are unchanged when each score is modified only at zero-mass outcomes or outside the enumerated support.
   Exact checked proposition: For all f f' g g', nonnegative sampled weights and positive-weight support equality of each score pair imply covariance f g = covariance f' g'.
   Premises and side conditions: Every listed outcome weight must be nonnegative. The sample may repeat outcomes, total mass need not equal one, and the covariance expressions are compared algebraically without independent-score assumptions.
   Proof/definition method: Expand covariance, then apply the checked expectation_extensional_on_positive_weight_support theorem to each marginal and to the pointwise product of the two scores. No new finite induction or matrix algorithm is used.
   Library reuse: expectation_extensional_on_positive_weight_support, FiniteSum.finite_sum_ext_in, Stdlib.List.In, Stdlib.Reals and ordered-field arithmetic.
   Boundary: Valid for an explicitly enumerated nonnegative weighted list; not a generic conditional expectation or almost-sure covariance result.
   *)
  Theorem covariance_extensional_on_positive_weight_support :
    forall f f' g g',
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x -> f x = f' x) ->
      (forall x, In x samples -> 0 < weight x -> g x = g' x) ->
      covariance f g = covariance f' g'.
  Proof.
    intros f f' g g' Hw Hf Hg.
    unfold covariance.
    rewrite (expectation_extensional_on_positive_weight_support
      f f' Hw Hf).
    rewrite (expectation_extensional_on_positive_weight_support
      g g' Hw Hg).
    assert (Hprod :
      expect (fun x => f x * g x) =
      expect (fun x => f' x * g' x)).
    { apply expectation_extensional_on_positive_weight_support.
      - exact Hw.
      - intros x Hx Hpositive.
        rewrite (Hf x Hx Hpositive), (Hg x Hx Hpositive).
        reflexivity. }
    rewrite Hprod.
    reflexivity.
  Qed.

  (**
   [variance_extensional_on_positive_weight_support] (theorem) — Nonnegative weighted finite support and covariance nullity.
   Mathematical meaning: A finite variance computed from nonnegative weights depends only on the score at positive-mass sample outcomes; changing values at zero-weight observations leaves its self-covariance unchanged.
   Exact checked proposition: For all f g, nonnegative sampled weights and equality on positive-weight sampled support imply variance f = variance g.
   Premises and side conditions: Nonnegative weights on the list are explicit, and no normalization, distinctness, or distributional model is assumed. Values of functions at zero-weight outcomes are unrestricted.
   Proof/definition method: Unfold variance as covariance of each score with itself and apply covariance_extensional_on_positive_weight_support with the same support equality for both arguments.
   Library reuse: covariance_extensional_on_positive_weight_support, FiniteMoments.variance, shared FiniteSum and Stdlib.List.In.
   Boundary: Signed weights are not supported by this positive-support extensionality criterion; no claim about continuous almost-sure equality is made.
   *)
  Theorem variance_extensional_on_positive_weight_support :
    forall f g,
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x -> f x = g x) ->
      variance f = variance g.
  Proof.
    intros f g Hw Hfg.
    unfold variance.
    apply covariance_extensional_on_positive_weight_support.
    - exact Hw.
    - exact Hfg.
    - exact Hfg.
  Qed.

  (**
   [covariance_zero_of_constant_on_positive_weight_support_first] (theorem) — Positive-support covariance/variance reuse.
   Mathematical meaning: If the first score agrees with a constant at every positively weighted sampled outcome, it has zero covariance with any comparison score, even if it differs from the constant outside the positive support.
   Exact checked proposition: For all f g and real c, total_mass = 1, nonnegative sampled weights, and f x = c at every listed outcome of positive weight imply covariance f g = 0.
   Premises and side conditions: No restriction on the comparison score or on zero-weight score values is imposed. The sample list may repeat outcomes; normalized nonnegative weights are explicitly required for the constant-score covariance law.
   Proof/definition method: Use covariance_extensional_on_positive_weight_support to replace the first argument by its constant representative, leaving the comparison score unchanged on the list; then invoke the existing covariance_with_constant_first theorem.
   Library reuse: covariance_extensional_on_positive_weight_support, covariance_with_constant_first, Stdlib.List.In and shared FiniteSum finite moments.
   Boundary: This is an exact finite weighted-support covariance result, not a statement of independence or covariance for signed, unnormalized measures.
   *)
  Theorem covariance_zero_of_constant_on_positive_weight_support_first :
    forall f g c,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x -> f x = c) ->
      covariance f g = 0.
  Proof.
    intros f g c Hmass Hw Hconstant.
    transitivity (covariance (fun _ => c) g).
    - apply covariance_extensional_on_positive_weight_support.
      + exact Hw.
      + exact Hconstant.
      + intros x Hx Hpositive; reflexivity.
    - apply covariance_with_constant_first; exact Hmass.
  Qed.

  (**
   [covariance_zero_of_constant_on_positive_weight_support_second] (theorem) — Positive-support covariance/variance reuse.
   Mathematical meaning: If the second score equals a constant on all positive-weight enumerated outcomes, covariance with any first score vanishes even when the second function has arbitrary values off that support.
   Exact checked proposition: For any f g c, under total_mass = 1 and nonnegative sampled weights, equality g x = c on positive-weight sampled outcomes entails covariance f g = 0.
   Premises and side conditions: The finite list may contain repeated outcomes and zero-weight entries; only positive-weight sampled values of g are constrained. No statistical independence assumption is introduced.
   Proof/definition method: Rewrite with the existing covariance_symmetric law to put the constant-on-support score first, then apply covariance_zero_of_constant_on_positive_weight_support_first.
   Library reuse: covariance_symmetric, covariance_zero_of_constant_on_positive_weight_support_first, Stdlib.Reals and FiniteSum.
   Boundary: Zero covariance alone is not an independence criterion; the conclusion holds in the finite weighted model only.
   *)
  Theorem covariance_zero_of_constant_on_positive_weight_support_second :
    forall f g c,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x -> g x = c) ->
      covariance f g = 0.
  Proof.
    intros f g c Hmass Hw Hconstant.
    rewrite covariance_symmetric.
    apply (covariance_zero_of_constant_on_positive_weight_support_first
      g f c Hmass Hw Hconstant).
  Qed.

  (**
   [variance_zero_of_constant_on_positive_weight_support] (theorem) — Nonnegative weighted finite support and covariance nullity.
   Mathematical meaning: A score that is constant at every outcome with positive sampled weight has variance zero under nonnegative normalized finite weights, regardless of arbitrary values at zero-weight outcomes.
   Exact checked proposition: For all f c, normalized total mass, nonnegative sampled weights and f x = c at every listed x with 0 < weight x entail variance f = 0.
   Premises and side conditions: The sample weights must sum to one and be nonnegative. The constant c may be any real number, and no assumption on the number of zero-weight outcomes or score independence is required.
   Proof/definition method: Unfold variance as self-covariance and apply the general covariance_zero_of_constant_on_positive_weight_support_first theorem directly. The previously duplicated variance extensionality and constant-score calculation is no longer necessary.
   Library reuse: covariance_zero_of_constant_on_positive_weight_support_first, FiniteMoments.variance, Stdlib.Reals and FiniteSum.
   Boundary: This finite constant-support criterion does not assert an empirical factor model or variance positivity for signed measures.
   *)
  Theorem variance_zero_of_constant_on_positive_weight_support :
    forall f c,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x -> f x = c) ->
      variance f = 0.
  Proof.
    intros f c Hmass Hw Hconstant.
    unfold variance.
    apply (covariance_zero_of_constant_on_positive_weight_support_first
      f f c Hmass Hw Hconstant).
  Qed.

  (**
   [variance_zero_iff_constant_on_positive_weight_support] (theorem) — Equivalences for exact finite covariance nullity.
   Mathematical meaning: Under normalized nonnegative finite weights, a score has zero variance exactly when it is equal to its own expectation on each sampled outcome carrying positive weight; zero-mass sample values are irrelevant.
   Exact checked proposition: For all f, total_mass = 1 and nonnegative sampled weights imply variance f = 0 iff every x in samples with 0 < weight x satisfies f x = expect f.
   Premises and side conditions: Unit total mass and nonnegative weight at every listed outcome are required. No individual strictly-positive weight, unique outcome, event independence or Gaussian assumption is imposed.
   Proof/definition method: The forward implication delegates to zero_variance_is_constant_on_positive_mass, while the converse is precisely variance_zero_of_constant_on_positive_weight_support with the constant chosen as expect f.
   Library reuse: zero_variance_is_constant_on_positive_mass, variance_zero_of_constant_on_positive_weight_support, FiniteSum and Stdlib.Reals.
   Boundary: The equivalence is exact for finite enumerated outcomes only; it is not a general spectral theorem or empirical statement about test scores.
   *)
  Theorem variance_zero_iff_constant_on_positive_weight_support :
    forall f,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (variance f = 0 <->
       forall x, In x samples -> 0 < weight x ->
         f x = expect f).
  Proof.
    intros f Hmass Hw.
    split.
    - intros Hzero x Hx Hpositive.
      apply (zero_variance_is_constant_on_positive_mass
        f x Hmass Hw Hzero Hx Hpositive).
    - intros Hconstant.
      apply (variance_zero_of_constant_on_positive_weight_support
        f (expect f) Hmass Hw Hconstant).
  Qed.

  (**
   [variance_zero_iff_exists_constant_on_positive_weight_support] (theorem) — Positive-support covariance/variance reuse.
   Mathematical meaning: Zero finite variance is equivalent to the existence of some real constant attained by the score on every positive-mass sampled outcome; the constant need not be supplied in advance.
   Exact checked proposition: For all f, when sample weights sum to one and are nonnegative, variance f = 0 iff exists c:R, forall x, In x samples -> 0 < weight x -> f x = c.
   Premises and side conditions: Strict positivity is only required for the outcomes on which score equality is asserted, not for every sample weight. Duplicated and zero-weight samples are permitted. Unit total mass ensures the existing zero-variance characterization applies.
   Proof/definition method: For the forward direction choose c = expect f and apply variance_zero_iff_constant_on_positive_weight_support. Conversely destruct the constant witness and invoke variance_zero_of_constant_on_positive_weight_support.
   Library reuse: variance_zero_iff_constant_on_positive_weight_support, variance_zero_of_constant_on_positive_weight_support, Stdlib.Logic and existing FiniteSum.
   Boundary: An exact existential support characterization for finite weighted scores; it does not compute empirical variance or prove a general measure-theoretic almost-sure statement.
   *)
  Theorem variance_zero_iff_exists_constant_on_positive_weight_support :
    forall f,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (variance f = 0 <->
       exists c : R,
         forall x, In x samples -> 0 < weight x -> f x = c).
  Proof.
    intros f Hmass Hw.
    split.
    - intros Hzero.
      exists (expect f).
      apply (proj1
        (variance_zero_iff_constant_on_positive_weight_support
          f Hmass Hw)).
      exact Hzero.
    - intros [c Hconstant].
      apply (variance_zero_of_constant_on_positive_weight_support
        f c Hmass Hw Hconstant).
  Qed.

  (**
   [variance_zero_iff_covariance_zero_with_every_score] (theorem) — Equivalences for exact finite covariance nullity.
   Mathematical meaning: With nonnegative normalized finite sample weights, a score has zero variance precisely when it is uncorrelated with every finite real-valued comparison score, including itself.
   Exact checked proposition: For every f, total_mass = 1 and nonnegative sampled weights imply variance f = 0 iff forall g, covariance f g = 0.
   Premises and side conditions: Normalization and nonnegative enumerated weights are essential for the forward direction via finite Cauchy–Schwarz. The reverse direction is purely definitional and does not require independence or positive individual variances.
   Proof/definition method: Use zero_variance_implies_zero_covariance_first for the forward direction, and instantiate the universal covariance-zero statement at g=f, where variance is definitionally self-covariance, for the reverse.
   Library reuse: zero_variance_implies_zero_covariance_first, FiniteMoments.variance and Stdlib.Reals.
   Boundary: This equivalence is restricted to the finite weighted covariance model, not a general Hilbert-space or measure-theoretic result.
   *)
  Theorem variance_zero_iff_covariance_zero_with_every_score :
    forall f,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (variance f = 0 <->
       forall g, covariance f g = 0).
  Proof.
    intros f Hmass Hw.
    split.
    - intros Hzero g.
      apply zero_variance_implies_zero_covariance_first;
        assumption.
    - intros Hall.
      unfold variance.
      apply Hall.
  Qed.

  (**
   [fixed_basis_null_iff_constant_on_positive_weight_support] (theorem) — Nonnegative weighted finite support and covariance nullity.
   Mathematical meaning: A real coefficient vector is a zero direction of the finite fixed-basis covariance quadratic form precisely when its weighted score is equal to its own expected value on every positive-mass enumerated outcome.
   Exact checked proposition: For any coefficients basis of equal length, with total_mass = 1 and nonnegative sampled weights, matrix_quadratic_form coefficients (basis_covariance_matrix basis) = 0 iff every sampled x with 0 < weight x satisfies weighted_basis_sum coefficients basis x = expect (weighted_basis_sum coefficients basis).
   Premises and side conditions: The coefficient and basis list lengths must agree. The total sample weight is one and every listed weight is nonnegative, but individual weights may equal zero; those outcomes impose no equality constraint on the score.
   Proof/definition method: Rewrite the covariance-matrix quadratic form as the weighted-score variance with fixed_basis_weighted_variance_identity, then apply the generic variance_zero_iff_constant_on_positive_weight_support theorem. Both directions now reuse one checked equivalence rather than duplicating the support proof.
   Library reuse: fixed_basis_weighted_variance_identity, variance_zero_iff_constant_on_positive_weight_support, FiniteSum and Stdlib.Reals.
   Boundary: This is a complete finite positive-support characterization of zero quadratic form, not a spectral matrix rank computation or an inference about empirical IQ factors.
   *)
  Theorem fixed_basis_null_iff_constant_on_positive_weight_support :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 <->
       forall x, In x samples -> 0 < weight x ->
         weighted_basis_sum coefficients basis x =
           expect (weighted_basis_sum coefficients basis)).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply variance_zero_iff_constant_on_positive_weight_support;
      assumption.
  Qed.


  (**
   [fixed_basis_null_iff_orthogonal_to_every_score] (theorem) — Equivalences for exact finite covariance nullity.
   Mathematical meaning: A finite fixed-basis covariance quadratic form vanishes exactly when the corresponding weighted basis score has zero covariance with every real-valued comparison score on the same finite weighted outcome space.
   Exact checked proposition: For all coefficients basis of equal length, total_mass=1 and nonnegative sampled weights imply matrix_quadratic_form coefficients (basis_covariance_matrix basis) = 0 iff forall g, covariance (weighted_basis_sum coefficients basis) g = 0.
   Premises and side conditions: The coefficient/basis list lengths must agree; sample weights are nonnegative and sum to one. No basis independence, nonsingular covariance matrix, or nonzero comparison variance is assumed.
   Proof/definition method: Rewrite the fixed-basis quadratic form as the variance of the same weighted score via fixed_basis_weighted_variance_identity and apply the fully general variance_zero_iff_covariance_zero_with_every_score theorem without reconstructing any matrix rows.
   Library reuse: fixed_basis_weighted_variance_identity, variance_zero_iff_covariance_zero_with_every_score, FiniteSum and Stdlib.Reals.
   Boundary: This exact finite null/orthogonality correspondence does not implement rank, characteristic polynomials, eigenvectors, or Gaussian score analysis.
   *)
  Theorem fixed_basis_null_iff_orthogonal_to_every_score :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 <->
       forall g, covariance (weighted_basis_sum coefficients basis) g = 0).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply variance_zero_iff_covariance_zero_with_every_score;
      assumption.
  Qed.


  (**
   [variance_positive_iff_not_constant_on_positive_weight_support] (theorem) — Finite positive variance and covariance curvature.
   Mathematical meaning: Under normalized nonnegative finite weights, variance is strictly positive exactly when the score is not equal to its expectation on every positive-weight enumerated outcome.
   Exact checked proposition: For any real score f, total_mass = 1 and nonnegative weights on samples entail 0 < variance f iff not(forall x in samples with positive weight, f x = expect f).
   Premises and side conditions: All sampled weights are nonnegative and total sampled mass is one; individual sampled weights may vanish and repeated sampled outcomes are counted with their multiplicity. The proof uses constructive real order decisions without postulating classical sample decidability.
   Proof/definition method: Combine the already verified finite variance_nonnegative bound with variance_zero_iff_constant_on_positive_weight_support; split on the standard real-order decision Rle_dec to eliminate the zero case.
   Library reuse: variance_nonnegative, variance_zero_iff_constant_on_positive_weight_support, Stdlib.Reals.Rle_dec and Stdlib.Lra.
   Boundary: This is an exact strictly-positive finite variance criterion, not a numerical lower bound or a claim about empirical IQ covariance.
   *)
  Theorem variance_positive_iff_not_constant_on_positive_weight_support :
    forall f,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < variance f <->
       ~ (forall x, In x samples -> 0 < weight x ->
          f x = expect f)).
  Proof.
    intros f Hmass Hw.
    pose proof (variance_nonnegative f Hmass Hw) as Hnonnegative.
    pose proof (variance_zero_iff_constant_on_positive_weight_support
      f Hmass Hw) as Hzero_iff.
    split.
    - intros Hpositive Hconstant.
      pose proof (proj2 Hzero_iff Hconstant) as Hzero.
      lra.
    - intro Hnonconstant.
      destruct (Rle_dec (variance f) 0) as [Hle | Hgt].
      + assert (Hzero : variance f = 0) by lra.
        exfalso.
        apply Hnonconstant.
        apply (proj1 Hzero_iff); exact Hzero.
      + lra.
  Qed.

  (**
   [variance_positive_iff_no_constant_on_positive_weight_support] (theorem) — Finite positive-support covariance degeneracy.
   Mathematical meaning: A finite normalized nonnegative weighted score has strictly positive variance precisely when there exists no real value at which the score is constant throughout all positively weighted sampled outcomes.
   Exact checked proposition: For any f, total_mass=1 and nonnegative weights on samples imply 0 < variance f iff not (exists c:R, forall x in samples with positive weight, f x=c).
   Premises and side conditions: Individual sample weights may equal zero and repeated sample entries retain their list multiplicity. The statement is exact and requires only a normalized finite nonnegative weighting, not independence or a Gaussian model.
   Proof/definition method: If variance is positive then any supported constant would force zero variance by variance_zero_of_constant_on_positive_weight_support, a contradiction. Conversely use variance_positive_iff_not_constant_on_positive_weight_support: constancy at the expectation would produce the forbidden existential witness.
   Library reuse: variance_zero_of_constant_on_positive_weight_support, variance_positive_iff_not_constant_on_positive_weight_support, Stdlib.Reals.Lra and existing finite moments.
   Boundary: The result does not compute a statistical estimate, prove any sample-size bound, or extend to signed or continuous measures.
   *)
  Theorem variance_positive_iff_no_constant_on_positive_weight_support :
    forall f,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < variance f <->
       ~ (exists c : R,
           forall x, In x samples -> 0 < weight x -> f x = c)).
  Proof.
    intros f Hmass Hw.
    split.
    - intros Hpositive [c Hconstant].
      pose proof (variance_zero_of_constant_on_positive_weight_support
        f c Hmass Hw Hconstant) as Hzero.
      lra.
    - intro Hno_constant.
      apply (proj2
        (variance_positive_iff_not_constant_on_positive_weight_support
          f Hmass Hw)).
      intro Hconstant.
      apply Hno_constant.
      exists (expect f).
      exact Hconstant.
  Qed.

  (**
   [fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support] (theorem) — Finite positive variance and covariance curvature.
   Mathematical meaning: A finite fixed-basis covariance quadratic form is strictly positive exactly when the coefficient-weighted basis score is not constant on its positive-mass sample support.
   Exact checked proposition: For all coefficient and basis lists of equal length, unit total mass and nonnegative sampled weights imply 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis) iff the weighted_basis_sum is not everywhere equal to its expectation on positive-weight sampled outcomes.
   Premises and side conditions: The coefficient vector and basis list must have identical lengths, total_mass must equal one, and weights must be nonnegative on the finite list. Neither basis independence nor strictly positive individual weights are assumed.
   Proof/definition method: Rewrite the existing covariance quadratic form into variance using fixed_basis_weighted_variance_identity, then apply the generic variance_positive_iff_not_constant_on_positive_weight_support without new matrix or finite-sum calculations.
   Library reuse: fixed_basis_weighted_variance_identity, variance_positive_iff_not_constant_on_positive_weight_support, Stdlib.List and Stdlib.Reals.
   Boundary: This certifies strict positivity in an individual coefficient direction; it does not assert that all nonzero directions are positive.
   *)
  Theorem fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) <->
       ~ (forall x, In x samples -> 0 < weight x ->
            weighted_basis_sum coefficients basis x =
              expect (weighted_basis_sum coefficients basis))).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply variance_positive_iff_not_constant_on_positive_weight_support;
      assumption.
  Qed.

  (**
   [positive_variance_of_positive_support_deviation] (theorem) — Strictly positive finite variance and covariance curvature.
   Mathematical meaning: A nonnegative normalized finite weighted score has strictly positive variance whenever a positive-weight sampled outcome has a score different from the finite expected score.
   Exact checked proposition: For any score f and sampled outcome x with 0 < weight x, normalized nonnegative sampled weights and f x <> expect f imply 0 < variance f.
   Premises and side conditions: Normalization and nonnegative sampled outcome weights are explicit. A strictly positive weight and membership for the witness x are required. No distributional model, continuous density or independence is assumed.
   Proof/definition method: Apply the stronger variance_positive_iff_not_constant_on_positive_weight_support theorem, then contradict the assumed positive-weight deviation with the hypothesized constant-score support property.
   Library reuse: variance_positive_iff_not_constant_on_positive_weight_support, Stdlib.List.In and standard real equality.
   Boundary: This theorem is about exact positive variance on a finite weighted list; it supplies no numerical lower bound or statistical inference from noisy observations.
   *)
  Theorem positive_variance_of_positive_support_deviation :
    forall f x,
      total_mass = 1 ->
      (forall y, In y samples -> 0 <= weight y) ->
      In x samples -> 0 < weight x ->
      f x <> expect f ->
      0 < variance f.
  Proof.
    intros f x Hmass Hw Hx Hpositive Hdeviation.
    apply (proj2
      (variance_positive_iff_not_constant_on_positive_weight_support
        f Hmass Hw)).
    intro Hconstant.
    apply Hdeviation.
    apply Hconstant; assumption.
  Qed.

  (**
   [positive_variance_of_two_distinct_positive_support_values] (theorem) — Strictly positive finite variance and covariance curvature.
   Mathematical meaning: Two enumerated outcomes with positive weights and different score values witness nonconstant positive-mass support and therefore imply strictly positive finite variance.
   Exact checked proposition: For all f x y, normalized nonnegative sampled weights, positive membership-weight premises for x and y, and f x <> f y imply 0 < variance f.
   Premises and side conditions: Both x and y must occur in the sample and receive strictly positive individual weights. Repeated outcome values are allowed in the list, but the stated score inequality ensures the two selected outcome values cannot coincide.
   Proof/definition method: Apply variance_positive_iff_not_constant_on_positive_weight_support. If the score were constant on positive-weight support, its values at both positive-weight witness outcomes would coincide by equality transitivity, contradicting the premise.
   Library reuse: variance_positive_iff_not_constant_on_positive_weight_support, Stdlib.List.In and equality transitivity.
   Boundary: The proof certifies strict variance positivity in the finite model but neither estimates its magnitude nor establishes any physical or empirical factor rank.
   *)
  Theorem positive_variance_of_two_distinct_positive_support_values :
    forall f x y,
      total_mass = 1 ->
      (forall z, In z samples -> 0 <= weight z) ->
      In x samples -> 0 < weight x ->
      In y samples -> 0 < weight y ->
      f x <> f y ->
      0 < variance f.
  Proof.
    intros f x y Hmass Hw Hx Hposx Hy Hposy Hdistinct.
    apply (proj2
      (variance_positive_iff_not_constant_on_positive_weight_support
        f Hmass Hw)).
    intro Hconstant.
    apply Hdistinct.
    transitivity (expect f).
    - apply Hconstant; assumption.
    - symmetry; apply Hconstant; assumption.
  Qed.

  (**
   [positive_fixed_basis_quadratic_of_positive_support_deviation] (theorem) — Strictly positive finite variance and covariance curvature.
   Mathematical meaning: The fixed-basis covariance matrix has strictly positive quadratic form in a coefficient direction whenever the resulting weighted score differs from its mean at a positive-mass sampled outcome.
   Exact checked proposition: For all coefficients basis x, equal coefficient/basis lengths, normalized nonnegative finite weights, positive sampled weight for x and weighted_basis_sum coefficients basis x <> expect (weighted_basis_sum coefficients basis) imply 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis).
   Premises and side conditions: The basis and coefficient dimensions must agree. The finite sampled weights are normalized and nonnegative, and the deviation witness x must be listed with strictly positive weight; no basis linear independence is assumed.
   Proof/definition method: Rewrite the quadratic form to the finite variance of weighted_basis_sum using fixed_basis_weighted_variance_identity, then invoke positive_variance_of_positive_support_deviation directly.
   Library reuse: fixed_basis_weighted_variance_identity, positive_variance_of_positive_support_deviation, Stdlib.List, FiniteSum and Stdlib.Lra.
   Boundary: This is a sufficient witness for strict quadratic positivity, not a general numeric eigenvalue lower bound or an assertion that the covariance matrix is positive definite.
   *)
  Theorem positive_fixed_basis_quadratic_of_positive_support_deviation :
    forall coefficients basis x,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall y, In y samples -> 0 <= weight y) ->
      In x samples -> 0 < weight x ->
      weighted_basis_sum coefficients basis x <>
        expect (weighted_basis_sum coefficients basis) ->
      0 < matrix_quadratic_form coefficients
        (basis_covariance_matrix basis).
  Proof.
    intros coefficients basis x Hlength Hmass Hw Hx Hpositive Hdeviation.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply (positive_variance_of_positive_support_deviation
      (weighted_basis_sum coefficients basis) x
      Hmass Hw Hx Hpositive Hdeviation).
  Qed.

  (**
   [positive_fixed_basis_quadratic_of_two_distinct_support_values] (theorem) — Strictly positive finite variance and covariance curvature.
   Mathematical meaning: If two positive-weight outcomes yield different weighted sums for a fixed score basis, then the covariance quadratic form in that coefficient direction is strictly positive.
   Exact checked proposition: For coefficients basis and x y, matching lengths, normalized nonnegative weights, positive enumerated x and y, and unequal weighted_basis_sum values at x and y entail strictly positive matrix_quadratic_form coefficients (basis_covariance_matrix basis).
   Premises and side conditions: The two positive-weight witnesses must occur in the explicitly enumerated list. The coefficient/basis dimensions agree, and repeated occurrences do not change the proof; no Gaussian or nondegeneracy assumption is imposed on the entire basis.
   Proof/definition method: Reuse the exact fixed_basis_weighted_variance_identity to convert the covariance matrix quadratic form into weighted-score variance, then directly apply positive_variance_of_two_distinct_positive_support_values.
   Library reuse: fixed_basis_weighted_variance_identity, positive_variance_of_two_distinct_positive_support_values, FiniteSum and Stdlib.Reals.
   Boundary: The conclusion certifies curvature in one tested coefficient direction only and does not yet prove full covariance-matrix rank or positive definiteness for every nonzero vector.
   *)
  Theorem positive_fixed_basis_quadratic_of_two_distinct_support_values :
    forall coefficients basis x y,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall z, In z samples -> 0 <= weight z) ->
      In x samples -> 0 < weight x ->
      In y samples -> 0 < weight y ->
      weighted_basis_sum coefficients basis x <>
        weighted_basis_sum coefficients basis y ->
      0 < matrix_quadratic_form coefficients
        (basis_covariance_matrix basis).
  Proof.
    intros coefficients basis x y Hlength Hmass Hw Hx Hposx Hy Hposy
      Hdistinct.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply (positive_variance_of_two_distinct_positive_support_values
      (weighted_basis_sum coefficients basis) x y
      Hmass Hw Hx Hposx Hy Hposy Hdistinct).
  Qed.


  (**
   [fixed_basis_positive_definite_iff_no_nonzero_constant_direction] (theorem) — Finite positive variance and covariance curvature.
   Mathematical meaning: For the repository's list-based real covariance matrices, positive definiteness in every nonzero compatible coefficient direction is equivalent to the absence of nonzero coefficient vectors producing a constant weighted score on the positive-weight sample support.
   Exact checked proposition: For any fixed basis under normalized nonnegative sampled weights, (forall coefficients of matching length different from Stdlib.List.repeat 0 (length basis), 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis)) iff (every such nonzero coefficient list fails to be equal to its own expected weighted score at all positive-weight sampled outcomes).
   Premises and side conditions: Total finite sample mass equals one and sampled weights are nonnegative. Only coefficient vectors of length equal to the basis length are considered, and nonzero is expressed through inequality from Stdlib.List.repeat 0. No uniqueness of outcomes or a positive-definite matrix hypothesis is assumed.
   Proof/definition method: Use the already proved fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support for the reverse implication; for the forward direction use fixed_basis_null_iff_constant_on_positive_weight_support to turn a hypothetical constant nonzero direction into a zero quadratic form, contradicting strict positivity by real linear arithmetic.
   Library reuse: Stdlib.List.repeat/length, fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support, fixed_basis_null_iff_constant_on_positive_weight_support, Stdlib.Lra.
   Boundary: This is an exact finite-list characterization of positive definiteness; it does not calculate a spectral rank or eigenvalues or claim empirical full-rank cognitive-test covariance.
   *)
  Theorem fixed_basis_positive_definite_iff_no_nonzero_constant_direction :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall coefficients,
          length coefficients = length basis ->
          coefficients <> repeat 0 (length basis) ->
          0 < matrix_quadratic_form coefficients
            (basis_covariance_matrix basis)) <->
       (forall coefficients,
          length coefficients = length basis ->
          coefficients <> repeat 0 (length basis) ->
          ~ (forall x, In x samples -> 0 < weight x ->
               weighted_basis_sum coefficients basis x =
                 expect (weighted_basis_sum coefficients basis)))).
  Proof.
    intros basis Hmass Hw.
    split; intros Hcriterion coefficients Hlength Hnonzero.
    - intro Hconstant.
      pose proof (Hcriterion coefficients Hlength Hnonzero)
        as Hpositive.
      pose proof (proj2
        (fixed_basis_null_iff_constant_on_positive_weight_support
          coefficients basis Hlength Hmass Hw) Hconstant)
        as Hzero.
      lra.
    - apply (proj2
        (fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support
          coefficients basis Hlength Hmass Hw)).
      apply Hcriterion; assumption.
  Qed.

  (**
   [fixed_basis_positive_definite_of_separating_positive_support_pairs] (theorem) — Finite positive-definite covariance criteria.
   Mathematical meaning: If every compatible nonzero coefficient vector separates two positive-weight sampled outcomes by their composite score values, then the fixed-basis finite covariance matrix has strictly positive quadratic form in every nonzero compatible direction.
   Exact checked proposition: For any basis with normalized nonnegative finite sample weights, if each coefficients list of matching length unequal to repeat 0 (length basis) admits sampled x,y of positive weight with different weighted_basis_sum values, then every such nonzero coefficients list has 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis).
   Premises and side conditions: Unit total mass, nonnegative sampled weights, matching coefficient/basis dimensions and an explicit pair of positive-weight support outcomes for each nonzero direction are required. Repeated outcomes and zero-weight observations are allowed; independence of basis scores is not assumed.
   Proof/definition method: Apply the supplied positive-support separation witness to a fixed nonzero direction, destruct the existential/and conjunctions, and invoke positive_fixed_basis_quadratic_of_two_distinct_support_values. This avoids constructing a separate rank or vector-space implementation.
   Library reuse: Stdlib.List.repeat, Stdlib.List.In, positive_fixed_basis_quadratic_of_two_distinct_support_values and the previously verified fixed-basis covariance representation.
   Boundary: This is a sufficient finite support separation condition for positive definiteness, not an algorithm for finding independent scores or assessing real-world IQ test validity.
   *)
  Theorem fixed_basis_positive_definite_of_separating_positive_support_pairs :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall coefficients,
        length coefficients = length basis ->
        coefficients <> repeat 0 (length basis) ->
        exists x y,
          In x samples /\ 0 < weight x /\
          In y samples /\ 0 < weight y /\
          weighted_basis_sum coefficients basis x <>
            weighted_basis_sum coefficients basis y) ->
      forall coefficients,
        length coefficients = length basis ->
        coefficients <> repeat 0 (length basis) ->
        0 < matrix_quadratic_form coefficients
          (basis_covariance_matrix basis).
  Proof.
    intros basis Hmass Hw Hseparates coefficients Hlength Hnonzero.
    destruct (Hseparates coefficients Hlength Hnonzero)
      as [x [y [Hx [Hposx [Hy [Hposy Hdistinct]]]]]].
    apply (positive_fixed_basis_quadratic_of_two_distinct_support_values
      coefficients basis x y Hlength Hmass Hw Hx Hposx
      Hy Hposy Hdistinct).
  Qed.

  (**
   [fixed_basis_positive_definite_of_positive_support_mean_deviations] (theorem) — Finite positive-definite covariance criteria.
   Mathematical meaning: If each compatible nonzero coefficient vector yields at least one positive-weight sampled score differing from its own finite expectation, the finite fixed-basis covariance matrix is positive definite.
   Exact checked proposition: For any basis with normalized nonnegative sampled weights, assume that for every compatible nonzero coefficients list there exists a sampled x with positive weight and weighted_basis_sum coefficients basis x <> expect (weighted_basis_sum coefficients basis); then every such coefficients list satisfies 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis).
   Premises and side conditions: Total mass must equal one, all sampled weights must be nonnegative and the coefficient vector must have the same length as the basis and differ from repeat 0. A positive-weight deviation witness is explicitly quantified for each nonzero direction.
   Proof/definition method: Instantiate the supplied witness at the desired coefficient list, and directly apply positive_fixed_basis_quadratic_of_positive_support_deviation. No new weighted expectation or matrix multiplication logic is introduced.
   Library reuse: positive_fixed_basis_quadratic_of_positive_support_deviation, Stdlib.List.repeat, Stdlib.List.In and the established FiniteMoments expected-value operator.
   Boundary: The condition guarantees strict curvature only in the finite covariance model. The theorem does not estimate a spectral gap, rank, or sample-based statistical uncertainty.
   *)
  Theorem fixed_basis_positive_definite_of_positive_support_mean_deviations :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall coefficients,
        length coefficients = length basis ->
        coefficients <> repeat 0 (length basis) ->
        exists x,
          In x samples /\ 0 < weight x /\
          weighted_basis_sum coefficients basis x <>
            expect (weighted_basis_sum coefficients basis)) ->
      forall coefficients,
        length coefficients = length basis ->
        coefficients <> repeat 0 (length basis) ->
        0 < matrix_quadratic_form coefficients
          (basis_covariance_matrix basis).
  Proof.
    intros basis Hmass Hw Hdeviations coefficients Hlength Hnonzero.
    destruct (Hdeviations coefficients Hlength Hnonzero)
      as [x [Hx [Hpositive Hdeviation]]].
    apply (positive_fixed_basis_quadratic_of_positive_support_deviation
      coefficients basis x Hlength Hmass Hw Hx Hpositive Hdeviation).
  Qed.

  (**
   [fixed_basis_positive_definite_iff_no_nonzero_orthogonal_direction] (theorem) — Finite positive-definite covariance criteria.
   Mathematical meaning: A fixed-basis finite covariance matrix is positive definite precisely when no compatible nonzero coefficient vector yields a composite score uncorrelated with every comparison score.
   Exact checked proposition: Under normalized nonnegative finite weights, (forall nonzero compatible coefficients, 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis)) iff (forall nonzero compatible coefficients, not(forall g, covariance (weighted_basis_sum coefficients basis) g = 0)).
   Premises and side conditions: Coefficients are nonzero by inequality with Stdlib.List.repeat 0 (length basis) and must match the finite basis length. Sampled weights are nonnegative and total mass equals one. No independence, eigenvalue, or full-support assumption is built into the theorem.
   Proof/definition method: The forward direction uses fixed_basis_null_iff_orthogonal_to_every_score to derive a contradiction between zero and strictly positive quadratic form. In the reverse direction, reduce strict quadratic positivity to support nonconstancy with fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support; if support were constant, the existing two nullity iff theorems would imply zero covariance with every comparison score, contradicting the hypothesis.
   Library reuse: fixed_basis_null_iff_orthogonal_to_every_score, fixed_basis_null_iff_constant_on_positive_weight_support, fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support, Stdlib.List.repeat and Stdlib.Lra.
   Boundary: This is a proposition-level characterization in the finite weighted covariance model and does not construct or calculate a matrix kernel basis, dimension, determinant, or spectral rank.
   *)
  Theorem fixed_basis_positive_definite_iff_no_nonzero_orthogonal_direction :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall coefficients,
          length coefficients = length basis ->
          coefficients <> repeat 0 (length basis) ->
          0 < matrix_quadratic_form coefficients
            (basis_covariance_matrix basis)) <->
       (forall coefficients,
          length coefficients = length basis ->
          coefficients <> repeat 0 (length basis) ->
          ~ (forall g,
              covariance (weighted_basis_sum coefficients basis) g = 0))).
  Proof.
    intros basis Hmass Hw.
    split; intros Hcriterion coefficients Hlength Hnonzero.
    - intro Hall.
      pose proof (Hcriterion coefficients Hlength Hnonzero) as Hpositive.
      pose proof (proj2
        (fixed_basis_null_iff_orthogonal_to_every_score
          coefficients basis Hlength Hmass Hw) Hall) as Hzero.
      lra.
    - apply (proj2
        (fixed_basis_positive_quadratic_iff_not_constant_on_positive_weight_support
          coefficients basis Hlength Hmass Hw)).
      intro Hconstant.
      apply (Hcriterion coefficients Hlength Hnonzero).
      apply (proj1
        (fixed_basis_null_iff_orthogonal_to_every_score
          coefficients basis Hlength Hmass Hw)).
      apply (proj2
        (fixed_basis_null_iff_constant_on_positive_weight_support
          coefficients basis Hlength Hmass Hw)).
      exact Hconstant.
  Qed.

  (**
   [fixed_basis_null_iff_exists_constant_on_positive_weight_support] (theorem) — Finite positive-support covariance degeneracy.
   Mathematical meaning: The exact finite covariance quadratic null directions are those coefficient lists whose weighted basis score equals some real constant at every positive-weight enumerated outcome.
   Exact checked proposition: For coefficient and basis lists of equal length under normalized nonnegative sampled weights, matrix_quadratic_form coefficients (basis_covariance_matrix basis)=0 iff exists c:R, forall positive-weight x in samples, weighted_basis_sum coefficients basis x=c.
   Premises and side conditions: Length equality, unit sample mass and nonnegative sampled weights are explicit. Zero-weight list entries need not agree with the constant, and the coefficient direction may be zero or nonzero.
   Proof/definition method: Use the existing fixed_basis_weighted_variance_identity to replace the quadratic form by the exact variance of the weighted basis score, then reuse variance_zero_iff_exists_constant_on_positive_weight_support without constructing new matrix operations.
   Library reuse: fixed_basis_weighted_variance_identity, variance_zero_iff_exists_constant_on_positive_weight_support, Stdlib.List and FiniteSum.
   Boundary: This equivalence characterizes null directions in the project's finite list covariance model; it is not an eigenvector or rank-nullity algorithm.
   *)
  Theorem fixed_basis_null_iff_exists_constant_on_positive_weight_support :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           weighted_basis_sum coefficients basis x = c).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply variance_zero_iff_exists_constant_on_positive_weight_support;
      assumption.
  Qed.

  (**
   [fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support] (theorem) — Finite positive-support covariance degeneracy.
   Mathematical meaning: Strictly positive finite covariance quadratic curvature in a compatible coefficient direction is equivalent to the impossibility of any single real constant matching its composite score on the entire positive-weight sampled support.
   Exact checked proposition: For matching coefficient/basis lengths, unit total mass and nonnegative sampled weights, 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis) iff not exists c:R constant for weighted_basis_sum coefficients basis on all positive-weight listed outcomes.
   Premises and side conditions: Normalization, sampled-weight nonnegativity and matching dimensions are required. Individual weights may vanish; no basis independence is assumed because this is a criterion for a particular direction.
   Proof/definition method: Apply the fixed_basis_weighted_variance_identity to rewrite the quadratic form into the variance of weighted_basis_sum, then invoke the generic variance_positive_iff_no_constant_on_positive_weight_support theorem.
   Library reuse: fixed_basis_weighted_variance_identity, variance_positive_iff_no_constant_on_positive_weight_support, Stdlib.Reals and shared FiniteSum.
   Boundary: The result does not imply an arbitrary covariance matrix is positive definite, nor does it provide a spectral rank calculation.
   *)
  Theorem fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) <->
       ~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             weighted_basis_sum coefficients basis x = c)).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    rewrite <- (fixed_basis_weighted_variance_identity
      coefficients basis Hlength Hmass).
    apply variance_positive_iff_no_constant_on_positive_weight_support;
      assumption.
  Qed.

  (**
   [duplicate_basis_covariance_not_positive_definite] (theorem) — Finite positive-support covariance degeneracy.
   Mathematical meaning: Two identical basis scores yield a finite covariance matrix that is never strictly positive in every nonzero coefficient direction under normalized sample weights: the nonzero difference vector [1,-1] has zero quadratic form.
   Exact checked proposition: For every f with total_mass=1, it is not the case that all compatible coefficient lists unequal to repeat 0 (length [f;f]) have strictly positive matrix_quadratic_form coefficients (basis_covariance_matrix [f;f]).
   Premises and side conditions: Only normalized finite total mass is assumed; even nonnegative sampled weights are unnecessary for this exact duplicated-score degeneracy. The zero vector uses Stdlib.List.repeat and the concrete two-component witness has matching dimensions.
   Proof/definition method: Reuse the earlier duplicate_basis_nontrivial_null_direction theorem to obtain the nonzero [1,-1] witness and zero quadratic form, convert the zero-list equality by standard list simplification, then contradict the proposed strict positive-definiteness condition with Lra.
   Library reuse: duplicate_basis_nontrivial_null_direction, Stdlib.List.repeat/length, Stdlib.Reals and Stdlib.Lra.
   Boundary: This proves an explicit duplicate-basis obstruction, not a general dimension or spectral rank theorem and not a claim about empirically near-duplicate tests.
   *)
  Theorem duplicate_basis_covariance_not_positive_definite :
    forall f,
      total_mass = 1 ->
      ~ (forall coefficients,
          length coefficients = length [f; f] ->
          coefficients <> repeat 0 (length [f; f]) ->
          0 < matrix_quadratic_form coefficients
            (basis_covariance_matrix [f; f])).
  Proof.
    intros f Hmass Hpositive_definite.
    destruct (duplicate_basis_nontrivial_null_direction f Hmass)
      as [Hnonzero Hnull].
    assert (Hnonzero_repeat :
      ([1; -1] : list R) <> repeat 0 (length [f; f])).
    { simpl. exact Hnonzero. }
    pose proof (Hpositive_definite [1; -1] eq_refl
      Hnonzero_repeat) as Hpositive.
    lra.
  Qed.

  (**
   [basis_cross_covariance_matrix_affine] (theorem) — Matrix-level affine covariance laws.
   Mathematical meaning: Applying the same affine score transformation to every score in a left finite basis and another affine transformation to each score in a right basis multiplies every cross-covariance matrix entry by the product of the two slopes; additive offsets disappear.
   Exact checked proposition: For any lists left right of real outcome scores, slopes a,c, offsets b,d and total_mass=1, basis_cross_covariance_matrix (map (fun f => fun x => a*f x+b) left) (map (fun g => fun x => c*g x+d) right) equals map (map (fun v => a*c*v)) (basis_cross_covariance_matrix left right).
   Premises and side conditions: Only the finite sample normalization total_mass = 1 is required; the result holds for signed weights, zero slopes, any real offsets, empty or repeated score lists, and rectangular matrices. No positive-weight, nonnegative-weight, or independence hypothesis is added.
   Proof/definition method: Introduce the entrywise scaled covariance matrix as an explicit intermediate list, use Stdlib.List.map_map to fuse each outer and inner mapping in a controlled order, then apply Stdlib.List.map_ext and the checked covariance_of_affine_scores equality to each entry.
   Library reuse: Stdlib.List.map_map, Stdlib.List.map_ext, covariance_of_affine_scores and the existing basis_cross_covariance_matrix definition.
   Boundary: This is exact finite-list entrywise covariance algebra; it is not a transformation of arbitrary matrices or a spectral rank theorem.
   *)
  Theorem basis_cross_covariance_matrix_affine :
    forall left right a b c d,
      total_mass = 1 ->
      basis_cross_covariance_matrix
        (map (fun f => fun x => a * f x + b) left)
        (map (fun g => fun x => c * g x + d) right) =
      map (map (fun v => a * c * v))
        (basis_cross_covariance_matrix left right).
  Proof.
    intros left right a b c d Hmass.
    unfold basis_cross_covariance_matrix.
    transitivity
      (map (fun f => map (fun g => a * c * covariance f g) right)
        left).
    - rewrite map_map.
      apply map_ext; intro f.
      rewrite map_map.
      apply map_ext; intro g.
      apply (covariance_of_affine_scores f g a b c d Hmass).
    - rewrite map_map.
      apply map_ext; intro f.
      rewrite map_map.
      reflexivity.
  Qed.

  (**
   [basis_covariance_matrix_affine] (theorem) — Matrix-level affine covariance laws.
   Mathematical meaning: The covariance matrix of a finite score basis transformed with a common slope and offset equals the original basis covariance matrix with every entry multiplied by the square of that slope, so a common offset cannot influence covariance.
   Exact checked proposition: For all finite score bases basis, real a b and total_mass=1, basis_covariance_matrix (map (fun f => fun x => a*f x+b) basis) = map (map (fun v => a*a*v)) (basis_covariance_matrix basis).
   Premises and side conditions: Unit total sampled mass is required for affine offset cancellation; otherwise weights may be signed, and the score list may be empty or contain duplicates. The same affine transformation applies to all basis scores.
   Proof/definition method: Regard the fixed-basis covariance matrix definitionally as the cross-covariance matrix with equal left and right score lists; apply basis_cross_covariance_matrix_affine with identical slopes and offsets. Avoid repeating either matrix-map proof or covariance algebra.
   Library reuse: basis_cross_covariance_matrix_affine, basis_covariance_matrix, basis_cross_covariance_matrix, Stdlib.List.map and Stdlib.Reals.
   Boundary: This proves entrywise finite covariance transformation, not positivity for signed weights or a general matrix spectral theorem.
   *)
  Theorem basis_covariance_matrix_affine :
    forall basis a b,
      total_mass = 1 ->
      basis_covariance_matrix
        (map (fun f => fun x => a * f x + b) basis) =
      map (map (fun v => a * a * v))
        (basis_covariance_matrix basis).
  Proof.
    intros basis a b Hmass.
    change
      (basis_cross_covariance_matrix
         (map (fun f => fun x => a * f x + b) basis)
         (map (fun f => fun x => a * f x + b) basis) =
       map (map (fun v => a * a * v))
         (basis_cross_covariance_matrix basis basis)).
    apply basis_cross_covariance_matrix_affine; exact Hmass.
  Qed.

  (**
   [affine_dependent_pair_nontrivial_null_on_positive_support] (theorem) — Affine-dependent finite covariance directions.
   Mathematical meaning: With nonnegative normalized sampled weights, the same nonzero coefficient direction [1;-a] is null even if f=a*g+c holds only where listed weights are strictly positive.
   Exact checked proposition: For all f g a c under mass-one nonnegative weights and positive-support affine equality, [1;-a]<>[0;0] and matrix_quadratic_form [1;-a] (basis_covariance_matrix [f;g])=0.
   Premises and side conditions: Each listed weight is nonnegative; the score equality need not hold at zero-weight outcomes. The slope may be zero and the basis may have repeated scores.
   Proof/definition method: Prove nontriviality with inversion/Lra; apply fixed_basis_null_iff_exists_constant_on_positive_weight_support with witness c, simplify the shared list-based linear combination and use the assumed support equality followed by ring.
   Library reuse: fixed_basis_null_iff_exists_constant_on_positive_weight_support, Stdlib.List.combine, FiniteSum.finite_sum, ring and Lra.
   Boundary: This is an exact two-score support-null result, not a general matrix kernel computation or numerical approximation.
   *)
  Theorem affine_dependent_pair_nontrivial_null_on_positive_support :
    forall f g a c,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x ->
        f x = a * g x + c) ->
      [1; -a] <> ([0; 0] : list R) /\
      matrix_quadratic_form [1; -a]
        (basis_covariance_matrix [f; g]) = 0.
  Proof.
    intros f g a c Hmass Hw Haffine.
    split.
    - intro Hzero.
      inversion Hzero; lra.
    - apply (proj2
        (fixed_basis_null_iff_exists_constant_on_positive_weight_support
          [1; -a] [f; g] eq_refl Hmass Hw)).
      exists c.
      intros x Hx Hpositive.
      unfold weighted_basis_sum, linear_combination,
        FiniteSum.finite_sum.
      simpl.
      rewrite (Haffine x Hx Hpositive).
      ring.
  Qed.

  (**
   [affine_dependent_pair_covariance_not_positive_definite] (theorem) — Affine-dependent finite covariance directions.
   Mathematical meaning: A two-score covariance matrix cannot be strictly positive definite when the scores are affine-dependent on the positive-weight sampled support: the nonzero [1;-a] direction has zero quadratic form.
   Exact checked proposition: For f g a c with normalized nonnegative sampled weights and f x=a*g x+c at positive-weight samples, not(all compatible coefficients differing from repeat 0 2 have strictly positive quadratic form in basis_covariance_matrix [f;g]).
   Premises and side conditions: The pair basis has length two, its weights are nonnegative and normalized, and zero-weight outcomes need not obey the affine relation. Nonzero is expressed with the library's Stdlib.List.repeat.
   Proof/definition method: Instantiate affine_dependent_pair_nontrivial_null_on_positive_support, simplify Stdlib.List.repeat, apply the hypothesized positive definiteness to [1;-a] and derive the inequality contradiction using Lra.
   Library reuse: affine_dependent_pair_nontrivial_null_on_positive_support, Stdlib.List.repeat, Stdlib.Lra.
   Boundary: Only an explicit finite two-dimensional obstruction is shown; general spectral matrix rank and empirical validity are outside the theorem.
   *)
  Theorem affine_dependent_pair_covariance_not_positive_definite :
    forall f g a c,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x ->
        f x = a * g x + c) ->
      ~ (forall coefficients,
          length coefficients = length [f; g] ->
          coefficients <> repeat 0 (length [f; g]) ->
          0 < matrix_quadratic_form coefficients
            (basis_covariance_matrix [f; g])).
  Proof.
    intros f g a c Hmass Hw Haffine Hpositive_definite.
    destruct (affine_dependent_pair_nontrivial_null_on_positive_support
      f g a c Hmass Hw Haffine) as [Hnonzero Hnull].
    assert (Hnonzero_repeat :
      ([1; -a] : list R) <> repeat 0 (length [f; g])).
    { simpl; exact Hnonzero. }
    pose proof (Hpositive_definite [1; -a] eq_refl
      Hnonzero_repeat) as Hpositive.
    lra.
  Qed.

  (**
   [fixed_basis_null_iff_uncorrelated_with_basis] (theorem) — Finite covariance coordinate nullspace criteria.
   Mathematical meaning: The quadratic form of a finite basis covariance matrix vanishes exactly when the corresponding coefficient-weighted score is uncorrelated with EACH member of that basis. Testing the coordinates suffices; testing all possible comparison scores is unnecessary.
   Exact checked proposition: For any equally long coefficient and basis lists under normalized nonnegative weights, matrix_quadratic_form coefficients (basis_covariance_matrix basis)=0 iff forall g, In g basis -> covariance (weighted_basis_sum coefficients basis) g=0.
   Premises and side conditions: Only matching lengths, unit total sample mass and nonnegative sampled weights are required. The basis can be empty or contain duplicates. For the converse, covariance linearity is purely algebraic; for the forward direction the existing finite covariance null theorem relies on nonnegative weights.
   Proof/definition method: For null-to-orthogonality, specialize fixed_basis_null_iff_orthogonal_to_every_score. Conversely rewrite the quadratic form as variance, interpret self-covariance as covariance with the original list combination, apply covariance_of_general_weighted_second_unconditional, then show every term of the existing FiniteSum.finite_sum row is zero by on-list extensionality. Stdlib.List.in_map and basis_of_combine transfer component membership to the basis; finite_sum_zero closes the proof.
   Library reuse: fixed_basis_null_iff_orthogonal_to_every_score, fixed_basis_weighted_variance_identity, covariance_of_general_weighted_second_unconditional, basis_of_combine, Stdlib.List.in_map, FiniteSum.finite_sum_ext_in, FiniteSum.finite_sum_zero, ring.
   Boundary: This is an exact finite-coordinate covariance criterion, not a computed matrix nullspace, a matrix-rank theorem or evidence about empirical IQ factors.
   *)
  Theorem fixed_basis_null_iff_uncorrelated_with_basis :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 <->
       forall g, In g basis ->
         covariance (weighted_basis_sum coefficients basis) g = 0).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    split.
    - intros Hnull g Hg.
      exact ((proj1
        (fixed_basis_null_iff_orthogonal_to_every_score
          coefficients basis Hlength Hmass Hw) Hnull) g).
    - intros Hbasis.
      rewrite <- (fixed_basis_weighted_variance_identity
        coefficients basis Hlength Hmass).
      unfold variance.
      change
        (covariance (weighted_basis_sum coefficients basis)
           (linear_combination (combine coefficients basis)) = 0).
      rewrite covariance_of_general_weighted_second_unconditional.
      unfold covariance_row.
      transitivity
        (FiniteSum.finite_sum
          (fun _ : R * (Outcome -> R) => 0)
          (combine coefficients basis)).
      + apply FiniteSum.finite_sum_ext_in.
        intros component Hcomponent.
        assert (Hin : In (snd component) basis).
        { rewrite <- (basis_of_combine coefficients basis Hlength).
          apply in_map.
          exact Hcomponent. }
        rewrite (Hbasis (snd component) Hin).
        ring.
      + apply FiniteSum.finite_sum_zero.
  Qed.

  (**
   [fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis] (theorem) — Finite covariance coordinate nullspace criteria.
   Mathematical meaning: A compatible direction has strictly positive covariance quadratic form exactly when its weighted score is NOT covariance-orthogonal to every basis score. This turns an all-comparison-score criterion into a finite coordinate-level test.
   Exact checked proposition: For matching coefficient/basis lengths, total_mass=1 and nonnegative sampled weights, 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis) iff not(forall g, In g basis -> covariance (weighted_basis_sum coefficients basis) g=0).
   Premises and side conditions: Unit mass, nonnegative listed weights and coefficient/basis length equality are necessary for the existing positive-semidefinite and nullity facts. No basis independence or covariance invertibility is assumed.
   Proof/definition method: Combine fixed_basis_covariance_matrix_positive_semidefinite with fixed_basis_null_iff_uncorrelated_with_basis. For strict positivity, use the decidable real comparison Rle_dec and Lra to rule out zero. The converse is a contradiction between positive and zero quadratic forms.
   Library reuse: fixed_basis_covariance_matrix_positive_semidefinite, fixed_basis_null_iff_uncorrelated_with_basis, Stdlib.Reals.Rle_dec, Stdlib.Lra.
   Boundary: The result is a logical characterization for a finite list covariance matrix; it does not calculate the entries' nullspace, rank or an eigenvalue lower bound.
   *)
  Theorem fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) <->
       ~ (forall g, In g basis ->
             covariance (weighted_basis_sum coefficients basis) g = 0)).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    pose proof (fixed_basis_covariance_matrix_positive_semidefinite
      basis coefficients Hlength Hmass Hw) as Hnonnegative.
    pose proof (fixed_basis_null_iff_uncorrelated_with_basis
      coefficients basis Hlength Hmass Hw) as Hnull_iff.
    split.
    - intros Hpositive Hall.
      pose proof (proj2 Hnull_iff Hall) as Hzero.
      lra.
    - intro Hnot_all.
      destruct (Rle_dec
        (matrix_quadratic_form coefficients
          (basis_covariance_matrix basis)) 0) as [Hle | Hgt].
      + assert (Hzero :
          matrix_quadratic_form coefficients
            (basis_covariance_matrix basis) = 0) by lra.
        exfalso.
        apply Hnot_all.
        apply (proj1 Hnull_iff); exact Hzero.
      + lra.
  Qed.

  (**
   [fixed_basis_positive_definite_iff_no_nonzero_basis_orthogonal_direction] (theorem) — Finite covariance coordinate nullspace criteria.
   Mathematical meaning: The finite covariance matrix is positive definite precisely when no nonzero compatible coefficient vector yields a composite score that is uncorrelated with EVERY basis score. Covariance tests against the finitely listed basis suffice, not all outcome-to-real comparison functions.
   Exact checked proposition: For any basis with unit total mass and nonnegative sampled weights, positive quadratic form for all coefficients of matching length distinct from repeat 0 (length basis) iff each such coefficient list fails the property forall g in basis, covariance (weighted_basis_sum coefficients basis) g=0.
   Premises and side conditions: The zero coefficient vector is represented by Stdlib.List.repeat, and compatibility is stated by list-length equality. The sample list may be empty only if the explicit mass-one/nonnegative premises remain satisfiable, and individual sample entries can have zero weight.
   Proof/definition method: Introduce an arbitrary nonzero compatible coefficient vector and apply the previously proved fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis in the appropriate direction of the iff, without constructing a new matrix multiplication or rank predicate.
   Library reuse: fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis, Stdlib.List.repeat/length, Stdlib.Reals and existing finite covariance definitions.
   Boundary: The characterization does not compute finite-dimensional rank or certify real-world score independence.
   *)
  Theorem fixed_basis_positive_definite_iff_no_nonzero_basis_orthogonal_direction :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall coefficients,
          length coefficients = length basis ->
          coefficients <> repeat 0 (length basis) ->
          0 < matrix_quadratic_form coefficients
            (basis_covariance_matrix basis)) <->
       (forall coefficients,
          length coefficients = length basis ->
          coefficients <> repeat 0 (length basis) ->
          ~ (forall g, In g basis ->
               covariance (weighted_basis_sum coefficients basis) g = 0))).
  Proof.
    intros basis Hmass Hw.
    split; intros Hproperty coefficients Hlength Hnonzero.
    - apply (proj1
        (fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis
          coefficients basis Hlength Hmass Hw)).
      apply Hproperty; assumption.
    - apply (proj2
        (fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis
          coefficients basis Hlength Hmass Hw)).
      apply Hproperty; assumption.
  Qed.

End FiniteProbabilityMoments.
