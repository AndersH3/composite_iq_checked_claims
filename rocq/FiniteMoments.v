(** Module: FiniteMoments.v
   Purpose: Finite weighted expectations, covariance algebra and score matrices.
   Derives moment linearity, variance bounds, composite-score covariance, and finite-list covariance-matrix formulas from a common finite sum.
   Mathematical representation: A fixed list of samples and a real weight function define expectation; covariance and variance are differences/products of expectations.
   Explicit hypotheses: Where a claim needs genuine probability, hypotheses require normalized total mass and nonnegative weights; vector identities require compatible list lengths.
   Library use: Stdlib.List, Sorting.Permutation, Vectors.Fin/Vector/VectorSpec, Reals and FiniteSum's reusable fold, extensionality, monotonicity and Fubini lemmas.
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
From Stdlib Require Vectors.Fin Vectors.Vector Vectors.VectorSpec.
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
   [vector_dot] (definition) — Finite coefficient dot product.
   Mathematical meaning: Multiply aligned entries of two real coefficient lists and sum those products. The shared List.combine operation pairs corresponding entries in their original order.
   Exact declaration: vector_dot xs ys := FiniteSum.finite_sum (fun p => fst p * snd p) (combine xs ys).
   Premises and side conditions: No vector-length equality is required by the definition. If the lengths differ, Stdlib.List.combine truncates to the shorter list; all theorems interpreting a full matrix row impose matching dimensions where necessary. All entries may be signed.
   Proof/definition method: This is a transparent alias of the shared generic real finite sum over Stdlib.List.combine, not a custom recursive dot product or matrix operation.
   Library reuse: Stdlib.List.combine and FiniteSum.finite_sum.
   Boundary: Defines a finite real-list operation, not a general finite-dimensional vector space or a norm.
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
   [matrix_bilinear_form] (definition) — Existing list-based finite matrix bilinear form.
   Mathematical meaning: For real coefficient lists u and v, compute the dot product of u with the list of rowwise dot products of v against each matrix row. This represents u-transpose M v for dimensionally compatible input lists.
   Exact declaration: matrix_bilinear_form left_coeffs right_coeffs matrix := vector_dot left_coeffs (map (vector_dot right_coeffs) matrix).
   Premises and side conditions: The definition does not demand rectangular rows or matching vector lengths. Since vector_dot uses Stdlib.List.combine, excess rows or entries are truncated according to the shorter input list. Theorems interpreting a full covariance bilinear form impose length compatibility.
   Proof/definition method: Compose the already defined vector_dot with Stdlib.List.map over the original rows; no nested index loops or new finite summation are implemented.
   Library reuse: Stdlib.List.map/combine, vector_dot, FiniteSum.finite_sum.
   Boundary: A concrete list-of-lists bilinear expression, not an arbitrary matrix algebra API or a rank/determinant theorem.
   *)
  Definition matrix_bilinear_form
    (left_coeffs right_coeffs : list R)
    (matrix : list (list R)) : R :=
    vector_dot left_coeffs (map (vector_dot right_coeffs) matrix).

  (**
   [matrix_quadratic_form] (definition) — Quadratic specialization of the existing bilinear form.
   Mathematical meaning: Evaluate the same real coefficient vector on both sides of the finite matrix: v-transpose M v. This is the exact expression used for covariance positive semidefiniteness and positive definiteness.
   Exact declaration: matrix_quadratic_form coeffs matrix := matrix_bilinear_form coeffs coeffs matrix.
   Premises and side conditions: Matrix shape and coefficient length are not checked by the definition; theorems about covariance matrices supply compatible coefficient/basis lengths. For an arbitrary matrix this quadratic value need not be nonnegative.
   Proof/definition method: Define by direct reuse of matrix_bilinear_form rather than duplicating matrix summation or dot-product logic.
   Library reuse: matrix_bilinear_form, vector_dot, Stdlib.List and FiniteSum.finite_sum.
   Boundary: The definition alone does not establish a covariance interpretation, PSD, rank or numerical spectral properties.
   *)
  Definition matrix_quadratic_form
    (coeffs : list R) (matrix : list (list R)) : R :=
    matrix_bilinear_form coeffs coeffs matrix.

  (**
   [covariance_row_as_vector_dot] (lemma) — Reuse the shared dot product for a weighted covariance row.
   Mathematical meaning: The finite sum of component coefficients times their covariance with a comparison score equals the dot product between the coefficient projection and covariance projection of the same component list.
   Exact checked proposition: forall f components, vector_dot (map fst components) (map (fun c => covariance f (snd c)) components) = covariance_row f components.
   Premises and side conditions: Both vectors are derived from the same component list, so lengths agree automatically even for an empty list. Coefficients, covariances, and outcome weights may all be signed; normalization is unnecessary.
   Proof/definition method: Unfold vector_dot and covariance_row, apply FiniteSum.finite_sum_zip_map to collapse Stdlib.List.combine of two matching maps, and finish by finite_sum_ext.
   Library reuse: FiniteSum.finite_sum_zip_map, FiniteSum.finite_sum_ext, Stdlib.List.map/combine.
   Boundary: Exact finite algebra only; not a claim about generic matrices or empirical covariance estimates.
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
   [weighted_basis_sum] (definition) — Coefficient-weighted composite of a finite score basis.
   Mathematical meaning: For lists [a1,...,an] and [f1,...,fn], evaluate the real score a1*f1(x)+...+an*fn(x) at outcome x via the shared coefficient-score combination.
   Exact declaration: weighted_basis_sum coefficients basis x := linear_combination (combine coefficients basis) x.
   Premises and side conditions: Coefficients may be signed and the basis may repeat functions. The definition permits unequal list lengths; Stdlib.List.combine truncates to the shorter list, so covariance matrix theorems explicitly require equal lengths.
   Proof/definition method: Pair the lists with Stdlib.List.combine, then reuse the existing FiniteSum-backed linear_combination; no independent list recursion or matrix implementation is added.
   Library reuse: Stdlib.List.combine, linear_combination, FiniteSum.finite_sum.
   Boundary: Exact finite composite scores; no latent-variable or empirical IQ-model assumptions follow from this definition.
   *)
  Definition weighted_basis_sum
    (coefficients : list R) (basis : list (Outcome -> R))
    (x : Outcome) : R :=
    linear_combination (combine coefficients basis) x.

  (**
   [basis_covariance_matrix] (definition) — Covariance matrix of a finite score basis.
   Mathematical meaning: For basis = [f1,...,fn], construct the n-by-n list of lists whose row i and column j contains covariance fi fj. All basis occurrences, including duplicates, retain their position.
   Exact declaration: basis_covariance_matrix basis := map (fun f => map (fun g => covariance f g) basis) basis.
   Premises and side conditions: The definition works with empty or repeated bases and signed, unnormalized sample weights; nonnegative unit-mass hypotheses are required only in positivity and probability theorems.
   Proof/definition method: Uses two levels of Stdlib.List.map, with scalar covariance supplied by the existing finite expectation model; no recursive matrix builder, indexing routine or copied sum is introduced.
   Library reuse: Stdlib.List.map, FiniteMoments.covariance, FiniteSum.finite_sum.
   Boundary: This constructs a square finite list-of-lists matrix and does not assert positive definiteness, eigenvalues or observed IQ covariance.
   *)
  Definition basis_covariance_matrix
    (basis : list (Outcome -> R)) : list (list R) :=
    map (fun f => map (fun g => covariance f g) basis) basis.

  (**
   [basis_cross_covariance_matrix] (definition) — Rectangular covariance between two score lists.
   Mathematical meaning: Build one covariance row for every score in left, with a column for each score in right; the resulting matrix has length left rows and length right entries per row.
   Exact declaration: basis_cross_covariance_matrix left right := map (fun f => map (fun g => covariance f g) right) left.
   Premises and side conditions: Lists can differ in length and may be empty or repeat scores. No weight sign or total-mass condition is necessary to construct the list; statistical positivity assumptions belong to individual theorems.
   Proof/definition method: Compose existing scalar covariance with nested Stdlib.List.map; the square basis_covariance_matrix is definitionally the equal-left-and-right case.
   Library reuse: Stdlib.List.map, FiniteMoments.covariance and shared FiniteSum.
   Boundary: A finite rectangular covariance representation, not a generic matrix transpose, multiplication or rank API.
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
   [basis_of_combine] (lemma) — Standard-library projection of paired coefficient and basis lists.
   Mathematical meaning: Combining equally long coefficient and score-basis lists and selecting each pair's second component recovers the original basis with the same ordering and multiplicity.
   Exact checked proposition: forall coefficients basis, length coefficients=length basis -> map snd (combine coefficients basis)=basis.
   Premises and side conditions: Length equality is required because Stdlib.List.combine otherwise truncates. No assumption on the numerical coefficients or score functions is made.
   Proof/definition method: Apply the already-checked combine_split inverse of List.combine, rewrite split_as_projection_maps and use f_equal snd to select the second list; no additional list induction is introduced.
   Library reuse: Stdlib.List.combine_split, split_as_projection_maps and f_equal.
   Boundary: A list-structural identity used to bridge covariance rows, not an arbitrary matrix-indexing result.
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
   [fixed_basis_weighted_variance_identity] (theorem) — Finite covariance quadratic form equals composite-score variance.
   Mathematical meaning: The variance of a coefficient-weighted finite score basis equals the coefficient vector's quadratic form against the covariance matrix of exactly that basis.
   Exact checked proposition: forall coefficients basis, length coefficients = length basis -> total_mass = 1 -> variance (weighted_basis_sum coefficients basis) = matrix_quadratic_form coefficients (basis_covariance_matrix basis).
   Premises and side conditions: Matching coefficient/basis lengths and unit sample mass are explicit. Individual outcome weights may be signed; positive-semidefinite and strict-positivity results separately require nonnegative sampled weights.
   Proof/definition method: Use weighted_basis_sum_as_combination to identify the composite score, invoke covariance_matrix_quadratic_form_is_variance on Stdlib.List.combine coefficients basis, then rewrite with coefficients_of_combine and fixed_basis_covariance_matrix_representation.
   Library reuse: covariance_matrix_quadratic_form_is_variance, variance_extensional, weighted_basis_sum_as_combination, coefficients_of_combine, fixed_basis_covariance_matrix_representation and Stdlib.List.combine.
   Boundary: Exact finite variance algebra, not a spectral decomposition or an empirical covariance assertion.
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
   [fixed_basis_covariance_matrix_positive_semidefinite] (theorem) — Nonnegative finite covariance quadratic forms.
   Mathematical meaning: For a normalized nonnegative weighted sample, every compatible real coefficient list has a nonnegative quadratic form against the covariance matrix of the chosen score basis.
   Exact checked proposition: forall basis coefficients, length coefficients=length basis -> total_mass=1 -> (forall x, In x samples -> 0<=weight x) -> 0<=matrix_quadratic_form coefficients (basis_covariance_matrix basis).
   Premises and side conditions: Coefficients and basis lengths must match. Sample weights sum to one and are individually nonnegative on enumerated outcomes. The result permits zero variance, repeated scores, and singular covariance matrices.
   Proof/definition method: Rewrite the matrix quadratic form as the variance of weighted_basis_sum using fixed_basis_weighted_variance_identity, then directly apply the prior variance_nonnegative theorem.
   Library reuse: fixed_basis_weighted_variance_identity, variance_nonnegative, FiniteSum and Stdlib.List.
   Boundary: Positive semidefiniteness does not imply positive definiteness; it supplies no numerical eigenvalue bounds or general rank statements.
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
   [zero_variance_is_constant_on_positive_mass] (theorem) — Zero finite variance forces constancy at positive-mass outcomes.
   Mathematical meaning: A zero-variance finite score equals its weighted expectation at every enumerated outcome whose sample weight is strictly positive. Zero-weight outcomes need not agree.
   Exact checked proposition: forall f x, total_mass = 1 -> (forall y, In y samples -> 0 <= weight y) -> variance f = 0 -> In x samples -> 0 < weight x -> f x = expect f.
   Premises and side conditions: Unit sampled total mass, nonnegative weights at all listed outcomes, zero variance and a positive-weight listed witness x are required. Repeated sample entries are allowed; no independence assumption is used.
   Proof/definition method: Rewrite variance zero using centered_second_moment_identity. Each weighted squared deviation is nonnegative by Rmult_le_pos and Rle_0_sqr; apply the shared sum_finite_zero_implies_zero_terms lemma at x. Positivity of weight x excludes the zero-weight factor, and Rmult_integral plus Lra forces the centered deviation to vanish.
   Library reuse: centered_second_moment_identity, sum_finite_zero_implies_zero_terms, Stdlib.Reals.Rmult_le_pos/Rle_0_sqr/Rmult_integral and Lra.
   Boundary: This statement concerns exact finite weighted support and does not assert a continuous almost-sure claim or numerical error tolerance.
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
   [fixed_basis_not_positive_definite_of_nonzero_null_direction] (theorem) — Finite covariance non-positive-definiteness.
   Mathematical meaning: Any compatible nonzero coefficient vector whose covariance quadratic form is zero disproves positive definiteness of the corresponding finite score-basis covariance matrix. This does not require nonnegative or normalized sample weights, because it is a direct contradiction with the strict inequality defining positive definiteness.
   Exact checked proposition: For any basis and coefficients with matching list lengths, coefficients <> repeat 0 (length basis), and matrix_quadratic_form coefficients (basis_covariance_matrix basis)=0, the universal strict positivity condition over all compatible nonzero coefficient lists is false.
   Premises and side conditions: Only list-length equality, the explicit nonzero witness, and quadratic nullity are assumed. Sample weights may be signed or unnormalized; the basis can be empty or contain repeated scores. Zero coefficient lists are represented with the standard Stdlib.List.repeat.
   Proof/definition method: Assume positive definiteness, instantiate it at the supplied coefficient list, and use Stdlib.Lra to contradict the checked equality between the quadratic value and zero. This factors out an identical argument previously repeated in the duplicate-score and affine-dependent-score obstructions.
   Library reuse: Stdlib.List.repeat/length, Stdlib.Reals.Lra, and the existing matrix_quadratic_form and basis_covariance_matrix definitions.
   Boundary: This is a logical obstruction, not a computed rank, determinant, eigenvalue or kernel basis; it does not assert any empirical score relation.
   *)
  Theorem fixed_basis_not_positive_definite_of_nonzero_null_direction :
    forall basis coefficients,
      length coefficients = length basis ->
      coefficients <> repeat 0 (length basis) ->
      matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) = 0 ->
      ~ (forall other,
          length other = length basis ->
          other <> repeat 0 (length basis) ->
          0 < matrix_quadratic_form other
            (basis_covariance_matrix basis)).
  Proof.
    intros basis coefficients Hlength Hnonzero Hnull Hpositive_definite.
    pose proof (Hpositive_definite coefficients Hlength Hnonzero)
      as Hpositive.
    lra.
  Qed.

  (**
   [fixed_basis_not_positive_definite_of_nonzero_constant_support_direction] (theorem) — Finite covariance non-positive-definiteness.
   Mathematical meaning: For normalized nonnegative sampled weights, any nonzero compatible coefficient vector yielding a constant composite score on the positive-weight support prevents the covariance matrix from being positive definite. The basis can have arbitrary finite length.
   Exact checked proposition: For any basis, coefficients and real constant c, matching list lengths, total_mass=1, nonnegative sampled weights, coefficients <> repeat 0 (length basis), and weighted_basis_sum coefficients basis x=c at every positive-weight listed x imply failure of strict positive definiteness.
   Premises and side conditions: Requires unit total sampled weight and nonnegative weights for the positive-support null-direction equivalence, but does not require positive weight at every sample. The nonzero vector is a supplied witness, not a computed vector.
   Proof/definition method: Use fixed_basis_null_iff_exists_constant_on_positive_weight_support to derive zero quadratic form from the supported constant c, then invoke fixed_basis_not_positive_definite_of_nonzero_null_direction. No independent covariance expansion or finite sum induction is needed.
   Library reuse: fixed_basis_null_iff_exists_constant_on_positive_weight_support, fixed_basis_not_positive_definite_of_nonzero_null_direction, Stdlib.List.repeat.
   Boundary: This is an exact finite support-degeneracy result without a general spectral rank calculation or any empirical inference.
   *)
  Theorem fixed_basis_not_positive_definite_of_nonzero_constant_support_direction :
    forall basis coefficients c,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      coefficients <> repeat 0 (length basis) ->
      (forall x, In x samples -> 0 < weight x ->
        weighted_basis_sum coefficients basis x = c) ->
      ~ (forall other,
          length other = length basis ->
          other <> repeat 0 (length basis) ->
          0 < matrix_quadratic_form other
            (basis_covariance_matrix basis)).
  Proof.
    intros basis coefficients c Hlength Hmass Hw Hnonzero Hconstant.
    apply (fixed_basis_not_positive_definite_of_nonzero_null_direction
      basis coefficients Hlength Hnonzero).
    apply (proj2
      (fixed_basis_null_iff_exists_constant_on_positive_weight_support
        coefficients basis Hlength Hmass Hw)).
    exists c.
    exact Hconstant.
  Qed.

  (**
   [duplicate_basis_covariance_not_positive_definite] (theorem) — Finite positive-support covariance degeneracy.
   Mathematical meaning: Two identical basis scores yield a finite covariance matrix that is never strictly positive in every nonzero coefficient direction under normalized sample weights: the nonzero difference vector [1,-1] has zero quadratic form.
   Exact checked proposition: For every f with total_mass=1, it is not the case that all compatible coefficient lists unequal to repeat 0 (length [f;f]) have strictly positive matrix_quadratic_form coefficients (basis_covariance_matrix [f;f]).
   Premises and side conditions: Only normalized finite total mass is assumed; even nonnegative sampled weights are unnecessary for this exact duplicated-score degeneracy. The zero vector uses Stdlib.List.repeat and the concrete two-component witness has matching dimensions.
   Proof/definition method: Obtain the nonzero coefficient list and zero quadratic form from duplicate_basis_nontrivial_null_direction, then apply the general fixed_basis_not_positive_definite_of_nonzero_null_direction theorem directly after Stdlib.List.repeat simplification. No locally duplicated strict-positivity contradiction is necessary.
   Library reuse: duplicate_basis_nontrivial_null_direction, fixed_basis_not_positive_definite_of_nonzero_null_direction, Stdlib.List.repeat.
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
    intros f Hmass.
    destruct (duplicate_basis_nontrivial_null_direction f Hmass)
      as [Hnonzero Hnull].
    apply (fixed_basis_not_positive_definite_of_nonzero_null_direction
      [f; f] [1; -1] eq_refl).
    - simpl; exact Hnonzero.
    - exact Hnull.
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
   Proof/definition method: Reuse the previously checked positive-support affine-dependent null witness and directly instantiate fixed_basis_not_positive_definite_of_nonzero_null_direction with [1;-a]. Stdlib.List.repeat simplification reconciles the explicit nonzero witness; the generic lemma handles the strict-positivity contradiction.
   Library reuse: affine_dependent_pair_nontrivial_null_on_positive_support, fixed_basis_not_positive_definite_of_nonzero_null_direction, Stdlib.List.repeat.
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
    intros f g a c Hmass Hw Haffine.
    destruct (affine_dependent_pair_nontrivial_null_on_positive_support
      f g a c Hmass Hw Haffine) as [Hnonzero Hnull].
    apply (fixed_basis_not_positive_definite_of_nonzero_null_direction
      [f; g] [1; -a] eq_refl).
    - simpl; exact Hnonzero.
    - exact Hnull.
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

  (**
   [covariance_with_weighted_basis_as_row_dot] (theorem) — Matrix-row covariance coordinates.
   Mathematical meaning: The covariance between an arbitrary comparison score and a weighted sum of a finite basis equals the dot product of the coefficient vector with the comparison score's covariance row over the same basis.
   Exact checked proposition: For all compatible coefficient/basis lists and comparison scores g, covariance g (weighted_basis_sum coefficients basis) = vector_dot coefficients (map (fun f => covariance g f) basis).
   Premises and side conditions: Only list-length compatibility is required; covariance bilinearity is an exact finite algebraic identity even when weights are signed or total_mass differs from one. No independence, positive weight, or nondegenerate covariance assumption is imposed.
   Proof/definition method: Expand weighted_basis_sum as the existing linear_combination; apply covariance_of_general_weighted_second_unconditional, then rewrite the covariance row using covariance_row_as_vector_dot. Stdlib.List.map_map fuses the covariance/snd projection; coefficients_of_combine and basis_of_combine normalize the two projections under length equality. No new list traversal is proved.
   Library reuse: covariance_of_general_weighted_second_unconditional, covariance_row_as_vector_dot, coefficients_of_combine, basis_of_combine, Stdlib.List.map_map and vector_dot.
   Boundary: This is a finite list-of-coordinates identity, not an assertion about general matrices or statistical population covariance.
   *)
  Theorem covariance_with_weighted_basis_as_row_dot :
    forall coefficients basis g,
      length coefficients = length basis ->
      covariance g (weighted_basis_sum coefficients basis) =
        vector_dot coefficients
          (map (fun f => covariance g f) basis).
  Proof.
    intros coefficients basis g Hlength.
    unfold weighted_basis_sum.
    rewrite covariance_of_general_weighted_second_unconditional.
    rewrite <- (covariance_row_as_vector_dot
      g (combine coefficients basis)).
    rewrite (coefficients_of_combine coefficients basis Hlength).
    replace
      (map (fun c => covariance g (snd c))
        (combine coefficients basis))
      with
      (map (fun f => covariance g f)
        (map snd (combine coefficients basis))).
    - rewrite (basis_of_combine coefficients basis Hlength).
      reflexivity.
    - rewrite map_map.
      reflexivity.
  Qed.

  (**
   [fixed_basis_null_iff_zero_dot_with_every_covariance_row] (theorem) — Matrix-row covariance coordinates.
   Mathematical meaning: A finite basis covariance quadratic form is zero exactly when the coefficient vector has zero dot product with each row of the actual list-of-lists covariance matrix. This is a direct matrix-row nullspace characterization without defining matrix multiplication or computing rank.
   Exact checked proposition: For compatible coefficients and basis, unit total_mass and nonnegative sampled weights, matrix_quadratic_form coefficients (basis_covariance_matrix basis)=0 iff forall row in basis_covariance_matrix basis, vector_dot coefficients row=0.
   Premises and side conditions: Total mass one, nonnegative sampled weights and coefficient/basis length equality are explicit; the basis may contain repeated scores and individual sample outcomes may have zero weight. Matrix rows can repeat because the list representation preserves multiplicity.
   Proof/definition method: Use fixed_basis_null_iff_uncorrelated_with_basis. For each matrix row, Stdlib.List.in_map_iff supplies its originating basis score; covariance_symmetric plus covariance_with_weighted_basis_as_row_dot gives zero dot product. Conversely construct the matching covariance-row membership with an explicit in_map_iff witness for the basis score, avoiding ambiguous inference of the nested map function, then apply the same bridge to obtain the coordinate covariance-zero premise.
   Library reuse: fixed_basis_null_iff_uncorrelated_with_basis, covariance_with_weighted_basis_as_row_dot, covariance_symmetric, Stdlib.List.in_map_iff and in_map.
   Boundary: This certifies a rowwise nullspace equivalence for the defined finite covariance matrix; it neither constructs a nullspace basis nor proves a spectral rank theorem.
   *)
  Theorem fixed_basis_null_iff_zero_dot_with_every_covariance_row :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (matrix_quadratic_form coefficients
         (basis_covariance_matrix basis) = 0 <->
       forall row, In row (basis_covariance_matrix basis) ->
         vector_dot coefficients row = 0).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    pose proof (fixed_basis_null_iff_uncorrelated_with_basis
      coefficients basis Hlength Hmass Hw) as Hcoordinate_iff.
    split.
    - intros Hnull row Hrow.
      unfold basis_covariance_matrix in Hrow.
      apply in_map_iff in Hrow.
      destruct Hrow as [g [Hrow_eq Hg]].
      subst row.
      rewrite <- (covariance_with_weighted_basis_as_row_dot
        coefficients basis g Hlength).
      rewrite (covariance_symmetric g
        (weighted_basis_sum coefficients basis)).
      exact ((proj1 Hcoordinate_iff Hnull) g Hg).
    - intros Hrows.
      apply (proj2 Hcoordinate_iff).
      intros g Hg.
      rewrite (covariance_symmetric
        (weighted_basis_sum coefficients basis) g).
      rewrite (covariance_with_weighted_basis_as_row_dot
        coefficients basis g Hlength).
      apply Hrows.
      unfold basis_covariance_matrix.
      apply in_map_iff.
      exists g.
      split.
      + reflexivity.
      + exact Hg.
  Qed.

  (**
   [fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot] (theorem) — Positive finite covariance matrix row criteria.
   Mathematical meaning: Strict positivity of a compatible finite covariance quadratic form is equivalent to the coefficient vector not being orthogonal to every row of its actual list-of-lists covariance matrix.
   Exact checked proposition: Under coefficient/basis length equality, unit sample mass and nonnegative sampled weights, 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis) iff not(forall row in basis_covariance_matrix basis, vector_dot coefficients row=0).
   Premises and side conditions: No nonzero-vector assumption is needed: the statement applies to each compatible coefficient vector, including zero. The sample can contain repeated or zero-weight outcomes, and matrix rows can duplicate scores.
   Proof/definition method: Combine fixed_basis_covariance_matrix_positive_semidefinite with fixed_basis_null_iff_zero_dot_with_every_covariance_row. In the forward direction, a zero-dot property contradicts strict positivity; in the reverse, Rle_dec and Lra show a nonnegative but nonpositive quadratic value must vanish, contradicting the rowwise negation.
   Library reuse: fixed_basis_covariance_matrix_positive_semidefinite, fixed_basis_null_iff_zero_dot_with_every_covariance_row, Stdlib.Reals.Rle_dec and Stdlib.Lra.
   Boundary: An exact finite rowwise criterion, not a numerical spectral gap, determinant or general matrix-rank computation.
   *)
  Theorem fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < matrix_quadratic_form coefficients
        (basis_covariance_matrix basis) <->
       ~ (forall row, In row (basis_covariance_matrix basis) ->
            vector_dot coefficients row = 0)).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    pose proof (fixed_basis_covariance_matrix_positive_semidefinite
      basis coefficients Hlength Hmass Hw) as Hnonnegative.
    pose proof (fixed_basis_null_iff_zero_dot_with_every_covariance_row
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
   [fixed_basis_positive_definite_iff_no_nonzero_covariance_row_kernel] (theorem) — Positive finite covariance matrix row criteria.
   Mathematical meaning: A finite covariance matrix is positive definite exactly when no nonzero coefficient vector of the appropriate length is orthogonal to all rows of that matrix, expressed using its existing list-based dot product.
   Exact checked proposition: For normalized nonnegative finite weights and any basis, forall coefficients of length equal to basis different from repeat 0 (length basis), matrix_quadratic_form coefficients (basis_covariance_matrix basis) is positive iff every such vector fails to have vector_dot coefficients row=0 for all matrix rows.
   Premises and side conditions: Compatibility and nonzero vectors are explicit, with zero represented by Stdlib.List.repeat. Nonnegative weights and total_mass=1 are assumed; a basis need not be linearly independent for the equivalence to hold as a conditional proposition.
   Proof/definition method: Fix an arbitrary nonzero compatible coefficient list in both directions of the iff and apply the rowwise fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot equivalence directly, without computing a nullspace or adding another matrix operation.
   Library reuse: fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot, Stdlib.List.repeat/length and the shared finite covariance matrix definitions.
   Boundary: This proves logical equivalence of positive definiteness and a trivial matrix-row kernel in this finite representation; it does not provide a rank, eigenvalue or kernel-basis algorithm.
   *)
  Theorem fixed_basis_positive_definite_iff_no_nonzero_covariance_row_kernel :
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
          ~ (forall row, In row (basis_covariance_matrix basis) ->
               vector_dot coefficients row = 0))).
  Proof.
    intros basis Hmass Hw.
    split; intros Hproperty coefficients Hlength Hnonzero.
    - apply (proj1
        (fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot
          coefficients basis Hlength Hmass Hw)).
      apply Hproperty; assumption.
    - apply (proj2
        (fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot
          coefficients basis Hlength Hmass Hw)).
      apply Hproperty; assumption.
  Qed.

  (**
   [fixed_basis_constant_support_implies_zero_covariance_row_dots] (theorem) — Exact covariance row-kernel witnesses.
   Mathematical meaning: If a coefficient-weighted basis score is constant on every positive-weight sampled outcome, then that coefficient vector is orthogonal to every actual row of its finite list-of-lists covariance matrix.
   Exact checked proposition: For any coefficients and basis of the same length under normalized nonnegative weights, if weighted_basis_sum coefficients basis x equals some c at every listed outcome with positive weight, then for all rows in basis_covariance_matrix basis, vector_dot coefficients row = 0.
   Premises and side conditions: Total sample mass equals one, sampled weights are nonnegative, and coefficient/basis lengths agree. Zero-weight samples may violate the equality; the vector may be zero or nonzero, and the matrix may include repeated rows.
   Proof/definition method: Apply the previously checked fixed_basis_null_iff_exists_constant_on_positive_weight_support using the supplied constant witness c, then apply fixed_basis_null_iff_zero_dot_with_every_covariance_row in the forward direction. No matrix multiplication, row recursion or new covariance expansion is needed.
   Library reuse: fixed_basis_null_iff_exists_constant_on_positive_weight_support, fixed_basis_null_iff_zero_dot_with_every_covariance_row, Stdlib.List.In.
   Boundary: This verifies exact finite covariance row constraints; it does not compute a kernel basis or establish empirical factor dependence.
   *)
  Theorem fixed_basis_constant_support_implies_zero_covariance_row_dots :
    forall coefficients basis c,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (forall x, In x samples -> 0 < weight x ->
        weighted_basis_sum coefficients basis x = c) ->
      forall row, In row (basis_covariance_matrix basis) ->
        vector_dot coefficients row = 0.
  Proof.
    intros coefficients basis c Hlength Hmass Hw Hconstant row Hrow.
    apply (proj1
      (fixed_basis_null_iff_zero_dot_with_every_covariance_row
        coefficients basis Hlength Hmass Hw)).
    - apply (proj2
        (fixed_basis_null_iff_exists_constant_on_positive_weight_support
          coefficients basis Hlength Hmass Hw)).
      exists c; exact Hconstant.
    - exact Hrow.
  Qed.

  (**
   [fixed_basis_not_positive_definite_of_nonzero_covariance_row_kernel] (theorem) — Exact covariance row-kernel witnesses.
   Mathematical meaning: A compatible nonzero coefficient vector that has zero dot product with every covariance-matrix row prevents the matrix from being positive definite. The proof promotes rowwise nullity to quadratic nullity using the previously checked finite covariance result.
   Exact checked proposition: For any coefficients and basis with equal lengths, total_mass=1 and nonnegative sampled weights, if coefficients differ from repeat 0 (length basis) and vector_dot coefficients row=0 for all rows of basis_covariance_matrix basis, the universal positive-definiteness property is false.
   Premises and side conditions: Nonnegative normalized weights are required for the row-nullity equivalence, while the final strict-positivity contradiction is purely algebraic. Repeated basis scores and zero-weight outcomes are allowed.
   Proof/definition method: Use the reverse direction of fixed_basis_null_iff_zero_dot_with_every_covariance_row to obtain a quadratic-null witness; apply fixed_basis_not_positive_definite_of_nonzero_null_direction to discharge the strict positive-definiteness negation. There is no independent list induction or real-order case analysis.
   Library reuse: fixed_basis_null_iff_zero_dot_with_every_covariance_row, fixed_basis_not_positive_definite_of_nonzero_null_direction, Stdlib.List.repeat.
   Boundary: The theorem exposes the finite covariance row-kernel obstruction but does not compute its dimension or imply a spectral rank theorem.
   *)
  Theorem fixed_basis_not_positive_definite_of_nonzero_covariance_row_kernel :
    forall basis coefficients,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      coefficients <> repeat 0 (length basis) ->
      (forall row, In row (basis_covariance_matrix basis) ->
        vector_dot coefficients row = 0) ->
      ~ (forall other,
          length other = length basis ->
          other <> repeat 0 (length basis) ->
          0 < matrix_quadratic_form other
            (basis_covariance_matrix basis)).
  Proof.
    intros basis coefficients Hlength Hmass Hw Hnonzero Hrows.
    apply (fixed_basis_not_positive_definite_of_nonzero_null_direction
      basis coefficients Hlength Hnonzero).
    apply (proj2
      (fixed_basis_null_iff_zero_dot_with_every_covariance_row
        coefficients basis Hlength Hmass Hw)).
    exact Hrows.
  Qed.

  (**
   [fixed_basis_zero_covariance_row_dots_iff_supported_constant] (theorem) — Exact finite covariance row/support characterization.
   Mathematical meaning: An arbitrary compatible coefficient vector is covariance-orthogonal to every row of the finite covariance matrix exactly when its composite score has some common real value on all positively weighted sampled outcomes.
   Exact checked proposition: For matching coefficient/basis lengths under total_mass=1 and nonnegative sampled weights, (forall row in basis_covariance_matrix basis, vector_dot coefficients row=0) iff exists c:R, forall sampled x of positive weight, weighted_basis_sum coefficients basis x=c.
   Premises and side conditions: Individual sample weights may be zero, in which case their scores need not equal the common constant. Repeated basis functions and sample occurrences are allowed. This does not assume the vector is nonzero.
   Proof/definition method: Compose the two previously checked biconditionals: fixed_basis_null_iff_zero_dot_with_every_covariance_row and fixed_basis_null_iff_exists_constant_on_positive_weight_support. Each direction passes through the same zero quadratic-form equality; no matrix operations are reconstructed.
   Library reuse: fixed_basis_null_iff_zero_dot_with_every_covariance_row, fixed_basis_null_iff_exists_constant_on_positive_weight_support, Stdlib.Logic.
   Boundary: An exact finite positive-support characterization of the row-dot kernel, not a computed matrix rank, nullspace basis or empirical score relation.
   *)
  Theorem fixed_basis_zero_covariance_row_dots_iff_supported_constant :
    forall coefficients basis,
      length coefficients = length basis ->
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall row, In row (basis_covariance_matrix basis) ->
          vector_dot coefficients row = 0) <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           weighted_basis_sum coefficients basis x = c).
  Proof.
    intros coefficients basis Hlength Hmass Hw.
    pose proof (fixed_basis_null_iff_zero_dot_with_every_covariance_row
      coefficients basis Hlength Hmass Hw) as Hrows.
    pose proof (fixed_basis_null_iff_exists_constant_on_positive_weight_support
      coefficients basis Hlength Hmass Hw) as Hconstant.
    split.
    - intro Hzero_rows.
      apply (proj1 Hconstant).
      apply (proj2 Hrows).
      exact Hzero_rows.
    - intro Hsupported_constant.
      apply (proj1 Hrows).
      apply (proj2 Hconstant).
      exact Hsupported_constant.
  Qed.

  (**
   [fixed_basis_positive_definite_iff_no_nonzero_supported_constant] (theorem) — Exact finite covariance row/support characterization.
   Mathematical meaning: A finite covariance matrix is positive definite precisely when no nonzero compatible coefficient vector yields any constant composite score on the positive-weight sample support. The constant is not required to equal a separately named expectation in the proposition.
   Exact checked proposition: For any basis with total_mass=1 and nonnegative sampled weights, (forall compatible coefficients <> repeat 0 (length basis), 0 < matrix_quadratic_form coefficients (basis_covariance_matrix basis)) iff for every such coefficient list, not exists c:R such that weighted_basis_sum coefficients basis equals c at all positive-weight sampled outcomes.
   Premises and side conditions: Unit total mass and nonnegative sampled weights are required for strict covariance positivity. The zero coefficient list is represented by Stdlib.List.repeat; compatibility is stated by matching lengths. No basis independence or distinct-sample assumption is added.
   Proof/definition method: Introduce each nonzero compatible coefficient list and project the already checked fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support theorem in the corresponding direction, avoiding any new real-order case analysis or matrix summation.
   Library reuse: fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support, Stdlib.List.repeat and Stdlib.Logic.
   Boundary: This is a finite positive-definiteness equivalence, not an algorithm for spectral rank, Gaussian factors or statistical validity.
   *)
  Theorem fixed_basis_positive_definite_iff_no_nonzero_supported_constant :
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
          ~ (exists c : R,
               forall x, In x samples -> 0 < weight x ->
                 weighted_basis_sum coefficients basis x = c))).
  Proof.
    intros basis Hmass Hw.
    split; intros Hproperty coefficients Hlength Hnonzero.
    - apply (proj1
        (fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support
          coefficients basis Hlength Hmass Hw)).
      apply Hproperty; assumption.
    - apply (proj2
        (fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support
          coefficients basis Hlength Hmass Hw)).
      apply Hproperty; assumption.
  Qed.


  (**
   [basis_covariance_matrix_as_cross] (theorem) — Square finite covariance matrix as a specialization of the rectangular covariance API.
   Mathematical meaning: The covariance matrix of one finite score basis is definitionally equal to the cross-covariance matrix obtained by using that same basis on both the row and column sides. This makes the shared rectangular representation the canonical entry point for subsequent dimension-indexed translations.
   Exact checked proposition: For any score basis list, basis_covariance_matrix basis = basis_cross_covariance_matrix basis basis, with the sample and weight parameters inherited from the FiniteProbabilityMoments section.
   Premises and side conditions: No assumption about score length, normalization, nonnegative weights, linear independence, or spectral rank is needed, and empty or duplicated bases are permitted.
   Proof/definition method: Close the equality by definitional computation because both existing definitions use the identical nested Stdlib.List.map of scalar covariance.
   Library reuse: basis_covariance_matrix, basis_cross_covariance_matrix, Stdlib.List.map, and the existing scalar covariance operator; no new square-matrix construction or summation is introduced.
   Boundary: Equality of finite list representations does not establish symmetry of an arbitrary matrix or identify matrix rank.
   *)
  Theorem basis_covariance_matrix_as_cross :
    forall basis,
      basis_covariance_matrix basis =
      basis_cross_covariance_matrix basis basis.
  Proof. reflexivity. Qed.

  (**
   [basis_cross_covariance_matrix_app_left] (theorem) — Covariance rows distribute over concatenating score lists.
   Mathematical meaning: Concatenating two lists of row-side scores and forming their cross-covariance matrix against the same column-side list is exactly the concatenation of the two existing cross-covariance matrices, preserving each row and all duplicate scores.
   Exact checked proposition: For left1 left2 right score lists, basis_cross_covariance_matrix (left1 ++ left2) right = basis_cross_covariance_matrix left1 right ++ basis_cross_covariance_matrix left2 right.
   Premises and side conditions: No matching lengths are required because the rectangular matrices have the same column basis. The weighted-sample model is unchanged, and neither normalized weights nor independence of scores is assumed.
   Proof/definition method: Unfold the already defined matrix constructor and invoke the standard library map_app equation, avoiding a project-specific induction or matrix-row append algorithm.
   Library reuse: Stdlib.List.map_app, basis_cross_covariance_matrix, Stdlib.List.app; all numeric cells still come from FiniteMoments.covariance.
   Boundary: This is a row-list representation identity and does not imply a block matrix rank formula or a covariance factorization.
   *)
  Theorem basis_cross_covariance_matrix_app_left :
    forall left1 left2 right,
      basis_cross_covariance_matrix (left1 ++ left2) right =
      basis_cross_covariance_matrix left1 right ++
      basis_cross_covariance_matrix left2 right.
  Proof.
    intros left1 left2 right.
    unfold basis_cross_covariance_matrix.
    rewrite map_app.
    reflexivity.
  Qed.

  (**
   [basis_cross_covariance_matrix_app_right] (theorem) — Covariance columns distribute over concatenating score lists.
   Mathematical meaning: Appending column-side score lists corresponds exactly to appending the two covariance row vectors for every score in the unchanged row-side basis. This result complements row append and identifies rectangular covariance block structure before any move to an indexed matrix library.
   Exact checked proposition: For all left right1 right2 score bases, basis_cross_covariance_matrix left (right1 ++ right2) = map (fun rowpair => fst rowpair ++ snd rowpair) (combine (basis_cross_covariance_matrix left right1) (basis_cross_covariance_matrix left right2)).
   Premises and side conditions: Both right-side lists are arbitrary and the row-side list is shared, so the two resulting matrices have the same row count. No normalization, nonnegative weights, distinctness or dimension parameters beyond the given lists are required.
   Proof/definition method: Induct on the original left-side list and use the standard library map_app identity for each row. This is a proof about the existing nested map and combine operators, not a new matrix-building algorithm.
   Library reuse: Stdlib.List.map_app, Stdlib.List.combine, basis_cross_covariance_matrix and ordinary list induction. No covariance expansion or dot-product recursion is introduced.
   Boundary: The equality is for the particular list-of-lists encoding of rectangular covariance matrices; it is not a general matrix multiplication or block rank theorem.
   *)
  Theorem basis_cross_covariance_matrix_app_right :
    forall left right1 right2,
      basis_cross_covariance_matrix left (right1 ++ right2) =
      map (fun rowpair => fst rowpair ++ snd rowpair)
        (combine (basis_cross_covariance_matrix left right1)
                 (basis_cross_covariance_matrix left right2)).
  Proof.
    intros left right1 right2.
    induction left as [|f fs IH].
    - reflexivity.
    - cbn [basis_cross_covariance_matrix map combine].
      rewrite map_app.
      f_equal.
      exact IH.
  Qed.

  (**
   [basis_cross_covariance_matrix_nth_error_entry] (theorem) — Dimension-safe positional access to a rectangular covariance cell.
   Mathematical meaning: If the ith left score and jth right score exist, then accessing the ith row and subsequently the jth entry of the rectangular covariance list returns exactly the scalar covariance of those two scores. Using Stdlib.List.nth_error preserves bounds information as Some rather than silently supplying a default value.
   Exact checked proposition: If nth_error left i = Some f, nth_error right j = Some g, and nth_error (basis_cross_covariance_matrix left right) i = Some row, then nth_error row j = Some (covariance f g).
   Premises and side conditions: Row and column index existence and the selected matrix row are all explicit through option-valued access. The indices may be any nat values for which the hypotheses hold. Neither weight nonnegativity nor finite-sample normalization is required.
   Proof/definition method: Unfold the existing nested map constructor only at the required row, use Stdlib.List.nth_error_map twice to read the selected score and score pair, and eliminate the equality of Some values without recomputing covariance.
   Library reuse: Stdlib.List.nth_error_map, Stdlib.Option.option_map, basis_cross_covariance_matrix, FiniteMoments.covariance. No custom indexing function, out-of-bounds default, or matrix entry recursion is introduced.
   Boundary: This certifies individual existing list-matrix entries, not a length-preserving equivalence with a full Fin-indexed algebra or a rank theorem.
   *)
  Theorem basis_cross_covariance_matrix_nth_error_entry :
    forall left right i j f g row,
      nth_error left i = Some f ->
      nth_error right j = Some g ->
      nth_error (basis_cross_covariance_matrix left right) i =
        Some row ->
      nth_error row j = Some (covariance f g).
  Proof.
    intros left right i j f g row Hf Hg Hrow.
    unfold basis_cross_covariance_matrix in Hrow.
    rewrite nth_error_map in Hrow.
    rewrite Hf in Hrow.
    simpl in Hrow.
    inversion Hrow; subst row.
    rewrite nth_error_map.
    rewrite Hg.
    reflexivity.
  Qed.

  (**
   [basis_cross_covariance_matrix_nth_error_swap] (theorem) — Scalar covariance symmetry at corresponding positions in transposed score lists.
   Mathematical meaning: Reading the covariance of the ith left score and jth right score from the left-right matrix returns the same real value as reading the jth right score and ith left score from the corresponding right-left matrix. This is the componentwise matrix transpose law, with all row and column indices explicitly certified by nth_error.
   Exact checked proposition: For left, right, naturals i,j, scores f,g and rows row_left,row_right, if nth_error left i=Some f, nth_error right j=Some g and each row is selected at its corresponding index, then nth_error row_left j = nth_error row_right i.
   Premises and side conditions: The four option-valued indexing hypotheses explicitly guarantee existing basis scores and matrix rows; there is no implicit out-of-bounds behavior, unit-mass premise or nonnegative-weight assumption.
   Proof/definition method: Rewrite both sides using the checked basis_cross_covariance_matrix_nth_error_entry theorem and apply the existing FiniteMoments.covariance_symmetric identity, avoiding hand-written transpose or nested list induction.
   Library reuse: basis_cross_covariance_matrix_nth_error_entry, covariance_symmetric and Stdlib.List.nth_error. A maintained matrix library can subsequently exploit this verified componentwise transport.
   Boundary: The theorem describes the score-basis covariance matrices only, not arbitrary matrices, matrix inversion, kernel dimensions or spectral decompositions.
   *)
  Theorem basis_cross_covariance_matrix_nth_error_swap :
    forall left right i j f g row_left row_right,
      nth_error left i = Some f ->
      nth_error right j = Some g ->
      nth_error (basis_cross_covariance_matrix left right) i =
        Some row_left ->
      nth_error (basis_cross_covariance_matrix right left) j =
        Some row_right ->
      nth_error row_left j = nth_error row_right i.
  Proof.
    intros left right i j f g row_left row_right
      Hf Hg Hleft Hright.
    rewrite (basis_cross_covariance_matrix_nth_error_entry
      left right i j f g row_left Hf Hg Hleft).
    rewrite (basis_cross_covariance_matrix_nth_error_entry
      right left j i g f row_right Hg Hf Hright).
    f_equal.
    apply covariance_symmetric.
  Qed.


  (**
   [basis_cross_covariance_matrix_nth_error_row] (theorem) — Selecting a valid matrix row gives the corresponding mapped covariances.
   Mathematical meaning: If the ith row score f is known through a successful nth_error lookup in a left basis, the ith row of the existing rectangular covariance matrix is exactly the list of covariances between f and every element of the right basis. This transports a finite-index witness from the basis to the matrix without choosing a default element.
   Exact checked proposition: For score lists left and right, natural i and score f, nth_error left i=Some f implies nth_error (basis_cross_covariance_matrix left right) i=Some (map (fun g => covariance f g) right).
   Premises and side conditions: The explicit Some hypothesis certifies that i is in the row-basis index domain. Right basis size is unrestricted; normalization, nonnegative weights and score independence are not assumed.
   Proof/definition method: Unfold the existing cross-covariance list constructor and rewrite with Stdlib.List.nth_error_map followed by the successful source basis lookup. The result is direct and does not repeat any covariance computation.
   Library reuse: Stdlib.List.nth_error_map, basis_cross_covariance_matrix and Stdlib.List.map; no custom row-indexing function or transpose algorithm is introduced.
   Boundary: The theorem is about an existing list-of-lists covariance matrix rather than a generic bounded matrix type or spectral rank property.
   *)
  Theorem basis_cross_covariance_matrix_nth_error_row :
    forall left right i f,
      nth_error left i = Some f ->
      nth_error (basis_cross_covariance_matrix left right) i =
        Some (map (fun g => covariance f g) right).
  Proof.
    intros left right i f Hf.
    unfold basis_cross_covariance_matrix.
    rewrite nth_error_map.
    rewrite Hf.
    reflexivity.
  Qed.

  (**
   [basis_cross_covariance_matrix_nth_error_row_length] (theorem) — Valid indexed covariance rows preserve their column dimension.
   Mathematical meaning: Every matrix row successfully selected through nth_error from the rectangular covariance of bases left and right has exactly length right columns. Unlike an unguarded nth list operation this is explicitly conditional on a valid row index and therefore cannot silently include an out-of-bounds default row.
   Exact checked proposition: If nth_error left i = Some f and nth_error (basis_cross_covariance_matrix left right) i=Some row, then length row=length right.
   Premises and side conditions: The successful basis and matrix row indexing operations certify the bounds. Score lists can be empty or duplicated and there is no assumption about normalized sample weights or covariance definiteness.
   Proof/definition method: Replace the indexed row using the previously checked basis_cross_covariance_matrix_nth_error_row identity, then invoke Stdlib.List.length_map for the covariance map over the right basis.
   Library reuse: basis_cross_covariance_matrix_nth_error_row, Stdlib.List.length_map and nth_error; no new matrix dimension recursion is written.
   Boundary: Rectangular row length preservation alone does not prove covariance rank, matrix inverse existence or a spectral decomposition.
   *)
  Theorem basis_cross_covariance_matrix_nth_error_row_length :
    forall left right i f row,
      nth_error left i = Some f ->
      nth_error (basis_cross_covariance_matrix left right) i = Some row ->
      length row = length right.
  Proof.
    intros left right i f row Hf Hrow.
    rewrite (basis_cross_covariance_matrix_nth_error_row
      left right i f Hf) in Hrow.
    inversion Hrow; subst row.
    apply length_map.
  Qed.

  (**
   [basis_covariance_matrix_nth_error_entry] (theorem) — Selected square covariance cell equals covariance of corresponding basis scores.
   Mathematical meaning: The ith row and jth column of the finite square covariance matrix are exactly the scalar covariance of the ith and jth basis scores whenever all positions are successfully selected by Stdlib.List.nth_error. This specializes the previously proved rectangular entry invariant to the square basis.
   Exact checked proposition: If nth_error basis i=Some f, nth_error basis j=Some g and nth_error (basis_covariance_matrix basis) i=Some row, then nth_error row j=Some (covariance f g).
   Premises and side conditions: The three option-valued lookups are explicit certificates of finite row and column indices. No separate normalization or weight positivity condition is needed for this exact list representation identity.
   Proof/definition method: Rewrite the square covariance matrix as the equal-basis instance of the rectangular matrix and invoke the previously proved nth_error entry theorem with identical left and right score lists.
   Library reuse: basis_covariance_matrix_as_cross, basis_cross_covariance_matrix_nth_error_entry and Stdlib.List.nth_error. No generic square matrix cell access routine is reimplemented.
   Boundary: This is a checked entry representation result; it does not assert positive definiteness, nonsingularity or the empirical validity of the covariance values.
   *)
  Theorem basis_covariance_matrix_nth_error_entry :
    forall basis i j f g row,
      nth_error basis i = Some f ->
      nth_error basis j = Some g ->
      nth_error (basis_covariance_matrix basis) i = Some row ->
      nth_error row j = Some (covariance f g).
  Proof.
    intros basis i j f g row Hf Hg Hrow.
    rewrite basis_covariance_matrix_as_cross in Hrow.
    eapply basis_cross_covariance_matrix_nth_error_entry;
      eassumption.
  Qed.

  (**
   [basis_covariance_matrix_nth_error_symmetric] (theorem) — Indexed entries of a square finite covariance matrix are symmetric.
   Mathematical meaning: The jth cell in the ith covariance row equals the ith cell in the jth row for every pair of valid basis positions. This is the directly observable symmetric-entry property of the existing list-based covariance matrix and will serve as the source-side invariant for a future indexed-matrix implementation.
   Exact checked proposition: Given nth_error basis i=Some f, nth_error basis j=Some g and both selected square matrix rows, nth_error row_i j=nth_error row_j i.
   Premises and side conditions: Bounds and row existence are represented by four explicit Some hypotheses; sample masses may be signed and need not be normalized because scalar covariance symmetry is algebraic.
   Proof/definition method: Rewrite both square matrix rows using basis_covariance_matrix_as_cross and instantiate the prior covariance-cross-matrix nth_error swap theorem with identical score bases. No manual transpose construction or entry arithmetic is required.
   Library reuse: basis_covariance_matrix_as_cross, basis_cross_covariance_matrix_nth_error_swap and the established covariance_symmetric theorem indirectly.
   Boundary: This verifies symmetry only for matrices constructed from the finite covariance operator, not for arbitrary matrices or for estimates with numerical rounding error.
   *)
  Theorem basis_covariance_matrix_nth_error_symmetric :
    forall basis i j f g row_i row_j,
      nth_error basis i = Some f ->
      nth_error basis j = Some g ->
      nth_error (basis_covariance_matrix basis) i = Some row_i ->
      nth_error (basis_covariance_matrix basis) j = Some row_j ->
      nth_error row_i j = nth_error row_j i.
  Proof.
    intros basis i j f g row_i row_j Hf Hg Hrow_i Hrow_j.
    rewrite basis_covariance_matrix_as_cross in Hrow_i.
    rewrite basis_covariance_matrix_as_cross in Hrow_j.
    eapply basis_cross_covariance_matrix_nth_error_swap;
      eassumption.
  Qed.


  (**
   [vector_of_list_nth_error] (theorem) — Library-based bridge between bounded vector indices and total option-valued list access.
   Mathematical meaning: Converting a finite list into Rocq's length-indexed Vector.of_list does not change its elements: for any index Fin.t (length xs), the corresponding natural index from Fin.to_nat successfully accesses the same value with Stdlib.List.nth_error as Vector.nth. The index's dependent type certifies that the list position exists, including the fact that no index inhabits an empty list.
   Exact checked proposition: forall T xs (i:Fin.t (length xs)), nth_error xs (proj1_sig (Fin.to_nat i)) = Some (Vector.nth (Vector.of_list xs) i).
   Premises and side conditions: The list is arbitrary and its element type T need not be inhabited or decidably comparable; index validity is guaranteed directly by the Fin.t type, not an additional runtime condition.
   Proof/definition method: Use the maintained VectorSpec.to_list_nth_order and VectorSpec.to_list_of_list_opp lemmas, the standard Fin.of_nat_to_nat_inv identity, and List.nth_error_nth' with the strict upper bound provided by Fin.to_nat. This avoids implementing a new vector/list conversion or an induction on bounded indices.
   Library reuse: Stdlib.Vectors.Fin, Vector, VectorSpec, Stdlib.List.nth_error_nth' and the existing List definition. No dependent indexing algorithm or new axiom is introduced.
   Boundary: This bridges the two standard finite collection representations only; covariance-specific algebra and matrix rank remain separate concerns.
   *)
  Theorem vector_of_list_nth_error :
    forall (T : Type) (xs : list T) (i : Fin.t (length xs)),
      nth_error xs (proj1_sig (Fin.to_nat i)) =
        Some (Vector.nth (Vector.of_list xs) i).
  Proof.
    intros T xs i.
    pose (Hbound := proj2_sig (Fin.to_nat i)).
    pose proof (VectorSpec.to_list_nth_order
      T (length xs) (Vector.of_list xs)
      (proj1_sig (Fin.to_nat i)) Hbound
      (Vector.nth (Vector.of_list xs) i)) as Hnth.
    unfold Vector.nth_order, Hbound in Hnth.
    rewrite Fin.of_nat_to_nat_inv in Hnth.
    rewrite VectorSpec.to_list_of_list_opp in Hnth.
    rewrite (@nth_error_nth' T xs
      (proj1_sig (Fin.to_nat i))
      (Vector.nth (Vector.of_list xs) i) Hbound).
    f_equal.
    symmetry.
    exact Hnth.
  Qed.

  (**
   [indexed_basis_cross_covariance_matrix] (definition) — Dimension-indexed rectangular covariance function using Rocq's standard finite vectors.
   Mathematical meaning: Represent a covariance matrix as a total function on one bounded row index and one bounded column index. Its row and column dimensions are exactly the lengths of the corresponding finite score-basis lists. Each cell is computed by the *existing* scalar covariance of the two scores selected by Vector.nth from Vector.of_list, eliminating every out-of-range default.
   Exact declaration: indexed_basis_cross_covariance_matrix left right : Fin.t (length left) -> Fin.t (length right) -> R := fun i j => covariance (Vector.nth (Vector.of_list left) i) (Vector.nth (Vector.of_list right) j).
   Premises and side conditions: The basis lists may be empty or contain duplicates. Fin.t 0 is uninhabited, so no extra empty-basis case or sentinel score is required. The covariance model keeps the original weighted sample unchanged and imposes no normalization requirement for the raw algebraic definition.
   Proof/definition method: Compose maintained Stdlib.Vectors.Vector.of_list and Vector.nth with the already checked finite scalar covariance function; there is no new index implementation, loop or row-major encoding.
   Library reuse: Stdlib.Vectors.Fin, Stdlib.Vectors.Vector, and the existing FiniteMoments.covariance operator.
   Boundary: A dimension-safe function matrix is not by itself a certified matrix rank/nullspace implementation, and no equality with the list representation is assumed without the entry bridge below.
   *)
  Definition indexed_basis_cross_covariance_matrix
      (left right : list (Outcome -> R)) :
      Fin.t (length left) -> Fin.t (length right) -> R :=
    fun i j =>
      covariance (Vector.nth (Vector.of_list left) i)
                 (Vector.nth (Vector.of_list right) j).

  (**
   [indexed_basis_cross_covariance_matrix_entry] (theorem) — Cellwise equivalence of the list covariance matrix and the dimension-indexed representation.
   Mathematical meaning: Reading a cell from an existing rectangular list covariance matrix at the bounded row and column indices encoded by Fin.t returns the entry of the new total Fin-indexed covariance function, establishing an exact bridge rather than merely assuming that the two representations match.
   Exact checked proposition: For score lists left right, Fin.t (length left) i, Fin.t (length right) j and a matrix row, if nth_error (basis_cross_covariance_matrix left right) (proj1_sig (Fin.to_nat i))=Some row, then nth_error row (proj1_sig (Fin.to_nat j))=Some (indexed_basis_cross_covariance_matrix left right i j).
   Premises and side conditions: Dimensions are enforced in the types of i and j and a successful row lookup is explicitly supplied, so no out-of-bounds row or column default is introduced. The result is algebraic for any original finite real sample weights.
   Proof/definition method: Invoke the previously verified rectangular nth_error entry characterization and discharge its two basis score lookup premises using the new vector_of_list_nth_error lemma, which itself delegates to maintained standard-library vector/list conversions.
   Library reuse: basis_cross_covariance_matrix_nth_error_entry, vector_of_list_nth_error, Stdlib.List.nth_error and Stdlib.Vectors.Fin/Vector.
   Boundary: This proves exact cell agreement at the valid index pair, not yet an isomorphism of entire matrix APIs, covariance rank or a determinant identity.
   *)
  Theorem indexed_basis_cross_covariance_matrix_entry :
    forall left right
           (i : Fin.t (length left))
           (j : Fin.t (length right)) row,
      nth_error (basis_cross_covariance_matrix left right)
        (proj1_sig (Fin.to_nat i)) = Some row ->
      nth_error row (proj1_sig (Fin.to_nat j)) =
        Some (indexed_basis_cross_covariance_matrix left right i j).
  Proof.
    intros left right i j row Hrow.
    unfold indexed_basis_cross_covariance_matrix.
    apply (basis_cross_covariance_matrix_nth_error_entry
      left right (proj1_sig (Fin.to_nat i))
      (proj1_sig (Fin.to_nat j))
      (Vector.nth (Vector.of_list left) i)
      (Vector.nth (Vector.of_list right) j) row).
    - apply vector_of_list_nth_error.
    - apply vector_of_list_nth_error.
    - exact Hrow.
  Qed.

  (**
   [indexed_basis_cross_covariance_matrix_swap] (theorem) — Transpose symmetry of the dimension-indexed finite covariance representation.
   Mathematical meaning: For any valid row index in the left score basis and column index in the right score basis, the finite-indexed covariance entry is unchanged by swapping both bases and their indices. This is a dimension-safe rectangular transpose law directly inherited from scalar covariance symmetry.
   Exact checked proposition: For left right score lists and i : Fin.t (length left), j : Fin.t (length right), indexed_basis_cross_covariance_matrix left right i j = indexed_basis_cross_covariance_matrix right left j i.
   Premises and side conditions: The indexed types supply all dimension bounds; there is no requirement that the matrices are square, that the weight model is normalized or nonnegative, or that the basis scores are independent.
   Proof/definition method: Unfold the dimension-indexed definition and invoke the already proved scalar covariance_symmetric theorem, avoiding implementation of a separate transposition routine or matrix index arithmetic.
   Library reuse: indexed_basis_cross_covariance_matrix, covariance_symmetric, Stdlib.Vectors.Vector.nth and Fin.t.
   Boundary: This is transpose symmetry of this particular covariance function, not a general theorem asserting symmetry of arbitrary rectangular matrices or a positive-definite covariance rank result.
   *)
  Theorem indexed_basis_cross_covariance_matrix_swap :
    forall left right
           (i : Fin.t (length left))
           (j : Fin.t (length right)),
      indexed_basis_cross_covariance_matrix left right i j =
      indexed_basis_cross_covariance_matrix right left j i.
  Proof.
    intros left right i j.
    unfold indexed_basis_cross_covariance_matrix.
    apply covariance_symmetric.
  Qed.


  (**
   [indexed_basis_cross_covariance_matrix_row] (theorem) — A bounded vector
   index selects a real row of the preexisting list covariance matrix.
   Mathematical meaning: Every dimension-safe left-basis index determines
   an actual list row containing exactly the covariances of that score
   against the right-basis scores, including duplicates and empty columns.
   Exact checked proposition: For any left and right score lists and
   i : Fin.t (length left), nth_error of the old cross-covariance matrix
   at proj1_sig (Fin.to_nat i) is Some (map (covariance selected_score) right).
   Premises and side conditions: Fin.t certifies the left index; no
   normalization, independence, square-shape or nonnegative weight is assumed.
   Proof/definition method: First translate the bounded vector index to the
   original list index, then reuse the preexisting row-selection theorem.
   Library reuse: vector_of_list_nth_error,
   basis_cross_covariance_matrix_nth_error_row, Stdlib.List.map,
   Stdlib.Vectors.Fin and Vector.
   Boundary: This is an exact row representation, not a determinant,
   matrix-rank computation or statement about continuous score models.
   *)
  Theorem indexed_basis_cross_covariance_matrix_row :
    forall left right (i : Fin.t (length left)),
      nth_error (basis_cross_covariance_matrix left right)
        (proj1_sig (Fin.to_nat i)) =
      Some (map
        (fun g => covariance
          (Vector.nth (Vector.of_list left) i) g) right).
  Proof.
    intros left right i.
    apply basis_cross_covariance_matrix_nth_error_row.
    apply vector_of_list_nth_error.
  Qed.

  (**
   [indexed_basis_cross_covariance_matrix_row_length] (theorem) —
   Every bounded covariance row has the expected number of columns.
   Mathematical meaning: A real row selected using a Fin.t index in the
   existing list matrix cannot be ragged or truncated; its length equals
   the number of scores in the right-hand basis.
   Exact checked proposition: For left right i row, with
   i : Fin.t (length left), a successful nth_error row lookup in
   basis_cross_covariance_matrix left right implies
   length row = length right.
   Premises and side conditions: The only row-bound premise is
   supplied by Fin.t; arbitrary finite weights and duplicate scores are
   permitted. No mass-one or positive-definiteness premise is required.
   Proof/definition method: Reuse the previously certified general
   row-length theorem after converting the bounded index to a source
   list lookup. No new induction or list traversal is implemented.
   Library reuse: basis_cross_covariance_matrix_nth_error_row_length,
   vector_of_list_nth_error and Stdlib.List.length_map.
   Boundary: Row shape agreement is not an assertion about linear rank
   or a generic matrix API.
   *)
  Theorem indexed_basis_cross_covariance_matrix_row_length :
    forall left right (i : Fin.t (length left)) row,
      nth_error (basis_cross_covariance_matrix left right)
        (proj1_sig (Fin.to_nat i)) = Some row ->
      length row = length right.
  Proof.
    intros left right i row Hrow.
    eapply basis_cross_covariance_matrix_nth_error_row_length.
    - apply vector_of_list_nth_error.
    - exact Hrow.
  Qed.

  (**
   [indexed_basis_cross_covariance_matrix_entry_total] (theorem) — Every bounded covariance index pair has a successful matching list-matrix cell.
   Mathematical meaning: Given any row index in Fin.t (length left) and column index in Fin.t (length right), there necessarily exists a corresponding row in the original list-of-lists covariance matrix, and accessing the indicated column of that row succeeds and returns the value of the new dimension-indexed matrix representation. This upgrades the previous conditional entry theorem into a total existence-and-equality bridge.
   Exact checked proposition: For any left and right score lists and i:Fin.t(length left), j:Fin.t(length right), there exists row such that nth_error (basis_cross_covariance_matrix left right) (proj1_sig (Fin.to_nat i)) = Some row and nth_error row (proj1_sig (Fin.to_nat j)) = Some (indexed_basis_cross_covariance_matrix left right i j).
   Premises and side conditions: The Fin.t index types enforce both dimensions, including the lack of indices for empty dimensions; no additional row-existence premise, default score, unit total mass or nonnegative sample weight is required. Scores may repeat, and the source finite sample remains exactly the same.
   Proof/definition method: Choose the original covariance row produced by Stdlib.List.map from the bounded left-basis score. The vector/list nth_error conversion certifies its original basis position, the checked basis row-selection theorem certifies its matrix-row position, and the previously proved indexed entry theorem certifies the matching cell.
   Library reuse: vector_of_list_nth_error, basis_cross_covariance_matrix_nth_error_row, indexed_basis_cross_covariance_matrix_entry, Stdlib.List.map/nth_error, and Stdlib.Vectors.Fin/Vector. No custom matrix indexing or re-enumeration is introduced.
   Boundary: This gives exact finite entry correspondence for the existing covariance construction, not an equivalence of arbitrary matrix algebra operators or a rank/nullspace theorem.
   *)
  Theorem indexed_basis_cross_covariance_matrix_entry_total :
    forall left right
           (i : Fin.t (length left))
           (j : Fin.t (length right)),
      exists row,
        nth_error (basis_cross_covariance_matrix left right)
          (proj1_sig (Fin.to_nat i)) = Some row /\
        nth_error row (proj1_sig (Fin.to_nat j)) =
          Some (indexed_basis_cross_covariance_matrix left right i j).
  Proof.
    intros left right i j.
    exists (map
      (fun g => covariance (Vector.nth (Vector.of_list left) i) g)
      right).
    split.
    - apply indexed_basis_cross_covariance_matrix_row.
    - apply indexed_basis_cross_covariance_matrix_entry.
      apply indexed_basis_cross_covariance_matrix_row.
  Qed.

  (**
   [indexed_basis_covariance_matrix_symmetric] (theorem) — Total symmetry of the dimension-indexed square covariance representation.
   Mathematical meaning: Every pair of valid bounded indices in a single finite score basis selects equal covariance entries in the opposite order. Unlike the earlier list-based symmetry statement, both entry lookups are total by construction, because they are functions on Fin.t (length basis) rather than potentially failing list positions.
   Exact checked proposition: For every basis and i,j : Fin.t(length basis), indexed_basis_cross_covariance_matrix basis basis i j = indexed_basis_cross_covariance_matrix basis basis j i.
   Premises and side conditions: The square shape is expressed by supplying the same basis to both dimensions, which also works for an empty basis (there can be no Fin.t 0 indices). No real-weight positivity, normalization, basis independence or invertibility premise is added.
   Proof/definition method: Instantiate the already verified rectangular indexed covariance swap identity with equal row and column bases. This reuses the scalar covariance symmetry proof indirectly and does not repeat any vector indexing or covariance algebra.
   Library reuse: indexed_basis_cross_covariance_matrix_swap, Stdlib.Vectors.Fin.t and the established FiniteMoments.covariance_symmetric result.
   Boundary: This is symmetry of a finite-indexed covariance function, not a certified generic matrix transpose, eigenvalue, determinant or spectral theorem.
   *)
  Theorem indexed_basis_covariance_matrix_symmetric :
    forall basis
           (i j : Fin.t (length basis)),
      indexed_basis_cross_covariance_matrix basis basis i j =
      indexed_basis_cross_covariance_matrix basis basis j i.
  Proof.
    intros basis i j.
    apply indexed_basis_cross_covariance_matrix_swap.
  Qed.


  (**
   [indexed_basis_covariance_matrix_diagonal] (theorem) —
   Diagonal covariance entries are variances for every bounded score index.
   Mathematical meaning: The diagonal of the dimension-indexed covariance
   matrix of a finite score basis is exactly the self-covariance (variance)
   of the selected score. This equality is algebraic even for signed weights.
   Exact checked proposition: For basis and i : Fin.t (length basis),
   indexed_basis_cross_covariance_matrix basis basis i i =
   variance (Vector.nth (Vector.of_list basis) i).
   Premises and side conditions: No normalization or nonnegative weight
   condition is required for this *equality*. Empty bases have no indices.
   Proof/definition method: Both sides reduce to covariance of the same
   selected score because variance is defined as self-covariance.
   Library reuse: FiniteMoments.variance and covariance, Stdlib.Vectors
   Fin.t and Vector.nth, without a separate diagonal traversal.
   Boundary: The definitional equality does not imply nonnegative
   variance until weight hypotheses are supplied in the next theorem.
   *)
  Theorem indexed_basis_covariance_matrix_diagonal :
    forall basis (i : Fin.t (length basis)),
      indexed_basis_cross_covariance_matrix basis basis i i =
      variance (Vector.nth (Vector.of_list basis) i).
  Proof.
    reflexivity.
  Qed.

  (**
   [indexed_basis_covariance_matrix_diagonal_nonnegative] (theorem) —
   Nonnegative diagonal entries under normalized nonnegative sample weights.
   Mathematical meaning: When the finite weighted sample is a probability
   distribution, every diagonal cell of the dimension-indexed basis
   covariance matrix is a nonnegative real number.
   Exact checked proposition: For basis and i : Fin.t (length basis),
   if total_mass = 1 and every sampled weight is nonnegative, then
   0 <= indexed_basis_cross_covariance_matrix basis basis i i.
   Premises and side conditions: The sample may contain duplicates and
   the basis may be linearly dependent; there is no positive-definiteness,
   independence or empirical-distribution assumption.
   Proof/definition method: Rewrite the diagonal entry as the existing
   variance and instantiate the previously proved finite variance
   nonnegativity theorem, preserving its explicit hypotheses.
   Library reuse: indexed_basis_covariance_matrix_diagonal,
   variance_nonnegative, Stdlib.Reals and Stdlib.Vectors.Fin.
   Boundary: This proves entrywise diagonal nonnegativity only, not
   the general matrix spectral theorem or certified matrix rank.
   *)
  Theorem indexed_basis_covariance_matrix_diagonal_nonnegative :
    forall basis (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <= indexed_basis_cross_covariance_matrix basis basis i i.
  Proof.
    intros basis i Hmass Hw.
    rewrite indexed_basis_covariance_matrix_diagonal.
    apply variance_nonnegative; assumption.
  Qed.



  (**
   [indexed_basis_cross_covariance_cauchy_schwarz_squared] (theorem) —
   Cauchy-Schwarz for a rectangular, dimension-safe covariance entry.
   Mathematical meaning: The squared covariance between a score from
   the left basis and a score from the right basis does not exceed
   the product of their two finite-sample score variances.
   Exact checked proposition: For arbitrary lists left and right,
   bounded indices i and j, and total_mass=1 with nonnegative sample
   weights, M(i,j)*M(i,j) <= variance(left[i])*variance(right[j]),
   where M is indexed_basis_cross_covariance_matrix left right.
   Premises and side conditions: Bases can have unequal dimensions,
   repeated scores or zero-variance components; independence and
   strictly positive variances are not premises.
   Proof/definition method: Unfold the indexed covariance entry only
   and apply the existing scalar finite Cauchy-Schwarz inequality.
   Library reuse: finite_covariance_cauchy_schwarz_squared,
   indexed_basis_cross_covariance_matrix, Stdlib.Vectors.Fin/Vector.
   Boundary: This proves coordinatewise squared covariance bounds;
   it is not a generic matrix spectral or determinant theorem.
   *)
  Theorem indexed_basis_cross_covariance_cauchy_schwarz_squared :
    forall left right
           (i : Fin.t (length left)) (j : Fin.t (length right)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix left right i j *
      indexed_basis_cross_covariance_matrix left right i j <=
      variance (Vector.nth (Vector.of_list left) i) *
      variance (Vector.nth (Vector.of_list right) j).
  Proof.
    intros left right i j Hmass Hw.
    unfold indexed_basis_cross_covariance_matrix.
    apply finite_covariance_cauchy_schwarz_squared; assumption.
  Qed.

  (**
   [indexed_basis_cross_covariance_nonzero_implies_positive_variances]
   (theorem) — A nonzero rectangular covariance requires both variances.
   Mathematical meaning: An indexed cross-covariance entry can be
   nonzero only when each of its selected scores has strictly positive
   variance under the same normalized nonnegative finite sample.
   Exact checked proposition: Given bounded i in left and j in right,
   total_mass=1, nonnegative sampled weights and M(i,j)<>0,
   both 0<variance(left[i]) and 0<variance(right[j]) follow.
   Premises and side conditions: No matching list lengths, independent
   basis functions, Gaussianity or matrix invertibility is required.
   Proof/definition method: Reduce the indexed entry to its
   definition, then apply the existing scalar nonzero-covariance theorem.
   Library reuse: nonzero_covariance_implies_positive_variances,
   indexed_basis_cross_covariance_matrix and Stdlib.Vectors.Fin/Vector.
   Boundary: Positive individual variances are necessary, not
   sufficient, for a nonzero covariance or full-rank matrix.
   *)
  Theorem indexed_basis_cross_covariance_nonzero_implies_positive_variances :
    forall left right
           (i : Fin.t (length left)) (j : Fin.t (length right)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix left right i j <> 0 ->
      0 < variance (Vector.nth (Vector.of_list left) i) /\
      0 < variance (Vector.nth (Vector.of_list right) j).
  Proof.
    intros left right i j Hmass Hw Hnonzero.
    unfold indexed_basis_cross_covariance_matrix in Hnonzero.
    apply nonzero_covariance_implies_positive_variances; assumption.
  Qed.

  (**
   [indexed_basis_cross_covariance_nonzero_implies_nonconstant_scores]
   (theorem) — Both selected scores vary on positive-weight support.
   Mathematical meaning: When cross-covariance between two selected
   scores is nonzero, neither score is constant across all the
   finite sample outcomes that actually carry positive mass.
   Exact checked proposition: For bounded rectangular indices i,j,
   unit total mass, nonnegative weights, and M(i,j)<>0, neither
   selected left nor selected right score has a constant value on
   every sampled x satisfying weight x>0.
   Premises and side conditions: Zero-weight outcomes need not obey
   any score equality; nonconstant scores can still have covariance
   zero, so the stated implication is intentionally one-way.
   Proof/definition method: Use the just-checked rectangular
   nonzero-covariance positive-variance theorem and the preexisting
   scalar strict-variance iff no-positive-support-constant theorem.
   Library reuse: indexed_basis_cross_covariance_nonzero_implies_positive_variances,
   variance_positive_iff_no_constant_on_positive_weight_support,
   Stdlib.Vectors.Vector.nth and Stdlib.Reals.
   Boundary: This is exact finite support variation, not empirical
   association, rank, causal or continuous-probability inference.
   *)
  Theorem indexed_basis_cross_covariance_nonzero_implies_nonconstant_scores :
    forall left right
           (i : Fin.t (length left)) (j : Fin.t (length right)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix left right i j <> 0 ->
      (~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             Vector.nth (Vector.of_list left) i x = c)) /\
      (~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             Vector.nth (Vector.of_list right) j x = c)).
  Proof.
    intros left right i j Hmass Hw Hnonzero.
    pose proof
      (indexed_basis_cross_covariance_nonzero_implies_positive_variances
        left right i j Hmass Hw Hnonzero) as [Hleft Hright].
    split.
    - apply (proj1
        (variance_positive_iff_no_constant_on_positive_weight_support
          (Vector.nth (Vector.of_list left) i) Hmass Hw)).
      exact Hleft.
    - apply (proj1
        (variance_positive_iff_no_constant_on_positive_weight_support
          (Vector.nth (Vector.of_list right) j) Hmass Hw)).
      exact Hright.
  Qed.

  (**
   [indexed_basis_covariance_matrix_cauchy_schwarz_squared] (theorem) —
   Squared Cauchy-Schwarz inequality for bounded covariance-matrix entries.
   Mathematical meaning: The square of the covariance between any two
   selected basis scores is bounded by the product of their diagonal
   entries. Both diagonals are variances of exactly the same scores.
   Exact checked proposition: For basis, i,j : Fin.t (length basis),
   normalized total mass and nonnegative sampled weights imply
   indexed covariance(i,j) * indexed covariance(i,j) <=
   indexed covariance(i,i) * indexed covariance(j,j).
   Premises and side conditions: The basis may contain repeated or
   dependent score functions. No strict positivity, Gaussian model,
   empirical correlation or matrix invertibility is assumed.
   Proof/definition method: Rewrite the two indexed diagonal cells
   as variances and specialize the more general rectangular indexed
   Cauchy-Schwarz theorem, avoiding a second scalar covariance reduction.
   Library reuse: indexed_basis_covariance_matrix_diagonal,
   indexed_basis_cross_covariance_cauchy_schwarz_squared,
   Stdlib.Vectors.Fin and Vector.
   Boundary: A coordinatewise squared bound is not a certified spectral
   decomposition or generic matrix rank theorem.
   *)
  Theorem indexed_basis_covariance_matrix_cauchy_schwarz_squared :
    forall basis (i j : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix basis basis i j *
      indexed_basis_cross_covariance_matrix basis basis i j <=
      indexed_basis_cross_covariance_matrix basis basis i i *
      indexed_basis_cross_covariance_matrix basis basis j j.
  Proof.
    intros basis i j Hmass Hw.
    rewrite !indexed_basis_covariance_matrix_diagonal.
    apply indexed_basis_cross_covariance_cauchy_schwarz_squared;
      assumption.
  Qed.

  (**
   [indexed_basis_covariance_matrix_diagonal_zero_iff_constant_on_support]
   (theorem) — Exact support characterization of a zero diagonal cell.
   Mathematical meaning: A basis-score variance vanishes exactly when
   that selected score is constant on all positive-weight sampled
   outcomes, even when zero-weight sample occurrences have other values.
   Exact checked proposition: Under total_mass=1 and nonnegative sampled
   weights, indexed covariance(i,i)=0 iff there exists c:R such that
   each sampled x with weight x>0 has Vector.nth selected_score i x=c.
   Premises and side conditions: The score-basis index is Fin.t-bounded;
   the original finite sample may contain duplicates and zero-weight
   outcomes, and no statistical or functional independence is assumed.
   Proof/definition method: Replace the indexed diagonal by the
   definitionally equal variance and apply the existing iff theorem
   describing zero variance on positive-weight support.
   Library reuse: indexed_basis_covariance_matrix_diagonal,
   variance_zero_iff_exists_constant_on_positive_weight_support,
   Stdlib.Vectors.Vector.nth and Stdlib.Reals.
   Boundary: This is a finite weighted-support statement; it does not
   compute nullity or rank of the indexed covariance matrix.
   *)
  Theorem indexed_basis_covariance_matrix_diagonal_zero_iff_constant_on_support :
    forall basis (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_cross_covariance_matrix basis basis i i = 0 <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           Vector.nth (Vector.of_list basis) i x = c).
  Proof.
    intros basis i Hmass Hw.
    rewrite indexed_basis_covariance_matrix_diagonal.
    apply variance_zero_iff_exists_constant_on_positive_weight_support;
      assumption.
  Qed.


  (**
   [indexed_basis_cross_covariance_zero_variance_row] (theorem) —
   Zero-variance scores annihilate rectangular covariance rows.
   Mathematical meaning: A score whose variance vanishes has covariance
   zero with every comparison score in any separate finite basis.
   Exact checked proposition: For left right and bounded indices i j,
   normalized nonnegative finite sample weights and variance of the
   selected left score equal to zero imply indexed covariance(i,j)=0.
   Premises and side conditions: The two bases may have different lengths,
   duplicates or zero-weight outcomes. No Gaussian or independence premise.
   Proof/definition method: Unfold only the indexed covariance function
   and apply the already verified scalar zero-variance covariance theorem.
   Library reuse: zero_variance_implies_zero_covariance_first,
   indexed_basis_cross_covariance_matrix, Stdlib.Vectors.Fin and Vector.
   Boundary: This establishes scalar entries, not generic matrix rank.
   *)
  Theorem indexed_basis_cross_covariance_zero_variance_row :
    forall left right
           (i : Fin.t (length left)) (j : Fin.t (length right)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      variance (Vector.nth (Vector.of_list left) i) = 0 ->
      indexed_basis_cross_covariance_matrix left right i j = 0.
  Proof.
    intros left right i j Hmass Hw Hzero.
    unfold indexed_basis_cross_covariance_matrix.
    apply zero_variance_implies_zero_covariance_first; assumption.
  Qed.

  (**
   [indexed_basis_cross_covariance_zero_variance_column] (theorem) —
   Zero-variance scores annihilate rectangular covariance columns.
   Mathematical meaning: Zero variance in a score selected from the
   right-hand basis forces covariance with every left score to be zero.
   Exact checked proposition: For any bounded left index i, right index
   j, normalized nonnegative weights, and variance(right[j])=0, the
   rectangular cross-covariance entry at i,j is zero.
   Premises and side conditions: Bases need not be square or independent;
   zero-weight outcomes and repeated scores remain permitted.
   Proof/definition method: Transpose the indexed rectangular covariance
   using its existing symmetry lemma, then apply the new row-zero result.
   Library reuse: indexed_basis_cross_covariance_matrix_swap,
   indexed_basis_cross_covariance_zero_variance_row, Stdlib.Vectors.Fin.
   Boundary: This is a finite exact identity, not a numerical nullspace.
   *)
  Theorem indexed_basis_cross_covariance_zero_variance_column :
    forall left right
           (i : Fin.t (length left)) (j : Fin.t (length right)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      variance (Vector.nth (Vector.of_list right) j) = 0 ->
      indexed_basis_cross_covariance_matrix left right i j = 0.
  Proof.
    intros left right i j Hmass Hw Hzero.
    rewrite indexed_basis_cross_covariance_matrix_swap.
    apply indexed_basis_cross_covariance_zero_variance_row; assumption.
  Qed.

  (**
   [indexed_basis_covariance_matrix_zero_diagonal_implies_zero_row]
   (theorem) — A vanishing diagonal cell forces a zero covariance row.
   Mathematical meaning: Under normalized nonnegative weights, a
   zero-variance selected basis score is uncorrelated with every score
   in the same basis. Thus all entries in its indexed matrix row vanish.
   Exact checked proposition: For bounded i,j in a finite score basis,
   total_mass=1, nonnegative sampled weights and indexed
   covariance(i,i)=0 imply indexed covariance(i,j)=0.
   Premises and side conditions: No basis independence or positive
   definiteness is assumed, and a zero-weight sampled outcome is not
   required to obey any constant-score property.
   Proof/definition method: Rewrite the zero diagonal as variance and
   specialize the more general rectangular zero-variance row theorem.
   Library reuse: indexed_basis_covariance_matrix_diagonal,
   indexed_basis_cross_covariance_zero_variance_row, Stdlib.Vectors.Vector.nth.
   Boundary: This proves row-level covariance nullity, not a general
   linear-algebraic rank-nullity identity.
   *)
  Theorem indexed_basis_covariance_matrix_zero_diagonal_implies_zero_row :
    forall basis (i j : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix basis basis i i = 0 ->
      indexed_basis_cross_covariance_matrix basis basis i j = 0.
  Proof.
    intros basis i j Hmass Hw Hzero.
    rewrite indexed_basis_covariance_matrix_diagonal in Hzero.
    apply indexed_basis_cross_covariance_zero_variance_row; assumption.
  Qed.


  (**
   [indexed_basis_covariance_matrix_zero_diagonal_implies_zero_column]
   (theorem) — Zero diagonal variance annihilates the corresponding column.
   Mathematical meaning: Every selected square covariance column is
   identically zero when its own score variance is zero.
   Exact checked proposition: Under unit mass and nonnegative sampled
   weights, indexed covariance(i,i)=0 implies indexed covariance(j,i)=0.
   Premises and side conditions: All indices are Fin.t-bounded; there is
   no score independence, strict weight positivity, or invertibility.
   Proof/definition method: Rewrite the diagonal as variance and invoke
   the rectangular zero-variance column result with equal bases.
   Library reuse: indexed_basis_covariance_matrix_diagonal,
   indexed_basis_cross_covariance_zero_variance_column, Stdlib.Vectors.Fin.
   Boundary: Zero columns are only coordinatewise finite nullity facts.
   *)
  Theorem indexed_basis_covariance_matrix_zero_diagonal_implies_zero_column :
    forall basis (i j : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix basis basis i i = 0 ->
      indexed_basis_cross_covariance_matrix basis basis j i = 0.
  Proof.
    intros basis i j Hmass Hw Hzero.
    rewrite indexed_basis_covariance_matrix_diagonal in Hzero.
    apply indexed_basis_cross_covariance_zero_variance_column; assumption.
  Qed.

  (**
   [indexed_basis_covariance_matrix_zero_row_iff_zero_diagonal] (theorem) —
   The diagonal characterizes an entirely zero indexed covariance row.
   Mathematical meaning: A zero row contains its zero diagonal, and
   zero variance of its score forces all row covariances to vanish.
   Exact checked proposition: For normalized nonnegative sample weights,
   (forall j : Fin.t (length basis), covariance(i,j)=0) iff
   indexed covariance(i,i)=0, for every bounded basis index i.
   Premises and side conditions: Duplicate scores and zero-weight samples
   are allowed. Strictly positive variance or rank is not assumed.
   Proof/definition method: One direction specializes j=i; the converse
   reuses the previous zero-diagonal-implies-zero-row theorem.
   Library reuse: indexed_basis_covariance_matrix_zero_diagonal_implies_zero_row,
   Stdlib.Vectors.Fin and core propositional proof rules.
   Boundary: This is not a general spectral matrix criterion.
   *)
  Theorem indexed_basis_covariance_matrix_zero_row_iff_zero_diagonal :
    forall basis (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall j : Fin.t (length basis),
          indexed_basis_cross_covariance_matrix basis basis i j = 0) <->
       indexed_basis_cross_covariance_matrix basis basis i i = 0).
  Proof.
    intros basis i Hmass Hw.
    split.
    - intro Hrow. apply Hrow.
    - intros Hzero j.
      apply indexed_basis_covariance_matrix_zero_diagonal_implies_zero_row;
        assumption.
  Qed.

  (**
   [indexed_basis_covariance_matrix_zero_column_iff_zero_diagonal]
   (theorem) — The diagonal characterizes an entirely zero covariance column.
   Mathematical meaning: Every coordinate in a square covariance column
   vanishes exactly when that column's score variance vanishes.
   Exact checked proposition: With unit total sample mass and nonnegative
   sampled weights, (forall j, indexed covariance(j,i)=0) iff
   indexed covariance(i,i)=0, for i : Fin.t (length basis).
   Premises and side conditions: The basis may be empty or dependent,
   with zero-weight sample occurrences and no invertibility premise.
   Proof/definition method: Specialize a zero column at j=i and use the
   previously proved zero-diagonal-to-zero-column implication backward.
   Library reuse: indexed_basis_covariance_matrix_zero_diagonal_implies_zero_column
   and Stdlib.Vectors.Fin; no independent covariance proof.
   Boundary: This exact coordinate criterion does not calculate rank.
   *)
  Theorem indexed_basis_covariance_matrix_zero_column_iff_zero_diagonal :
    forall basis (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall j : Fin.t (length basis),
          indexed_basis_cross_covariance_matrix basis basis j i = 0) <->
       indexed_basis_cross_covariance_matrix basis basis i i = 0).
  Proof.
    intros basis i Hmass Hw.
    split.
    - intro Hcolumn. apply Hcolumn.
    - intros Hzero j.
      apply indexed_basis_covariance_matrix_zero_diagonal_implies_zero_column;
        assumption.
  Qed.

  (**
   [indexed_basis_covariance_matrix_principal_minor_nonnegative] (theorem) —
   Two-coordinate principal covariance minors are nonnegative.
   Mathematical meaning: For every pair of bounded basis indices, the
   expression representing their 2-by-2 covariance determinant is >= 0.
   Exact checked proposition: Under unit total mass and nonnegative
   sampled weights, 0 <= M(i,i)*M(j,j) - M(i,j)*M(j,i), where M denotes
   indexed_basis_cross_covariance_matrix basis basis.
   Premises and side conditions: The indices may coincide; no positive
   definiteness or independent basis scores are required.
   Proof/definition method: Rewrite M(j,i) to M(i,j) using indexed
   symmetry, specialize the existing Cauchy-Schwarz bound, then use lra.
   Library reuse: indexed_basis_covariance_matrix_symmetric,
   indexed_basis_covariance_matrix_cauchy_schwarz_squared, Stdlib.Lra.
   Boundary: Only two-coordinate principal minors are certified;
   generic matrix determinants and spectral rank remain unproved.
   *)
  Theorem indexed_basis_covariance_matrix_principal_minor_nonnegative :
    forall basis (i j : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <=
        indexed_basis_cross_covariance_matrix basis basis i i *
        indexed_basis_cross_covariance_matrix basis basis j j -
        indexed_basis_cross_covariance_matrix basis basis i j *
        indexed_basis_cross_covariance_matrix basis basis j i.
  Proof.
    intros basis i j Hmass Hw.
    rewrite (indexed_basis_covariance_matrix_symmetric basis j i).
    pose proof
      (indexed_basis_covariance_matrix_cauchy_schwarz_squared
        basis i j Hmass Hw) as Hcs.
    lra.
  Qed.


  (**
   [indexed_basis_covariance_matrix_zero_row_iff_zero_column] (theorem) —
   Null rows and columns agree in a symmetric indexed covariance matrix.
   Mathematical meaning: All entries of a selected covariance row
   vanish precisely when all entries of the corresponding column vanish.
   Exact checked proposition: For any basis and i : Fin.t (length basis),
   (forall j, indexed covariance(i,j)=0) iff
   (forall j, indexed covariance(j,i)=0).
   Premises and side conditions: This is algebraic covariance symmetry,
   with no normalization, nonnegative weight, nonempty basis,
   Gaussian distribution or statistical independence assumption.
   Proof/definition method: Rewrite each cell by the established
   indexed square covariance symmetry theorem in opposite directions.
   Library reuse: indexed_basis_covariance_matrix_symmetric,
   Stdlib.Vectors.Fin and core propositional reasoning.
   Boundary: Symmetry relates coordinates but does not certify a
   numerical matrix rank, determinant or general nullspace algorithm.
   *)
  Theorem indexed_basis_covariance_matrix_zero_row_iff_zero_column :
    forall basis (i : Fin.t (length basis)),
      (forall j : Fin.t (length basis),
        indexed_basis_cross_covariance_matrix basis basis i j = 0) <->
      (forall j : Fin.t (length basis),
        indexed_basis_cross_covariance_matrix basis basis j i = 0).
  Proof.
    intros basis i.
    split; intros Hzero j.
    - rewrite (indexed_basis_covariance_matrix_symmetric basis j i).
      apply Hzero.
    - rewrite (indexed_basis_covariance_matrix_symmetric basis i j).
      apply Hzero.
  Qed.

  (**
   [indexed_basis_covariance_matrix_zero_row_iff_constant_on_support]
   (theorem) — Exact constant-score criterion for an indexed zero row.
   Mathematical meaning: A covariance row vanishes exactly when the
   score it represents is constant over every outcome with positive
   weight in the enumerated finite sample.
   Exact checked proposition: Under unit total mass and nonnegative
   sampled weights, all covariance(i,j)=0 over bounded j iff
   exists c:R, forall x in samples with weight x>0, selected_score i x=c.
   Premises and side conditions: The claim permits repeated score basis
   elements, repeated outcomes, and different values at zero-weight
   outcomes. No invertibility or score independence is assumed.
   Proof/definition method: Compose the existing zero-row iff zero
   diagonal result with the established diagonal iff positive-support
   constant characterization, using propositional transitivity (tauto).
   Library reuse: indexed_basis_covariance_matrix_zero_row_iff_zero_diagonal,
   indexed_basis_covariance_matrix_diagonal_zero_iff_constant_on_support,
   Stdlib.Vectors.Vector.nth and the standard tauto tactic.
   Boundary: This is exact finite support behavior, not a statement
   about continuous random variables or generic matrix nullity.
   *)
  Theorem indexed_basis_covariance_matrix_zero_row_iff_constant_on_support :
    forall basis (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall j : Fin.t (length basis),
          indexed_basis_cross_covariance_matrix basis basis i j = 0) <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           Vector.nth (Vector.of_list basis) i x = c).
  Proof.
    intros basis i Hmass Hw.
    pose proof
      (indexed_basis_covariance_matrix_zero_row_iff_zero_diagonal
        basis i Hmass Hw) as Hrow.
    pose proof
      (indexed_basis_covariance_matrix_diagonal_zero_iff_constant_on_support
        basis i Hmass Hw) as Hconstant.
    tauto.
  Qed.

  (**
   [indexed_basis_covariance_matrix_zero_column_iff_constant_on_support]
   (theorem) — Exact constant-score criterion for an indexed zero column.
   Mathematical meaning: Every covariance with one selected score as
   second coordinate is zero exactly when that score is constant on
   the finite sample's positive-weight support.
   Exact checked proposition: For a bounded basis index i and normalized
   nonnegative weights, all covariance(j,i)=0 over bounded j iff there
   is c:R equal to selected_score i x at every positive-weight sample x.
   Premises and side conditions: This assumes neither matrix
   invertibility nor positive variance and places no restriction on
   zero-weight occurrences beyond nonnegative weights.
   Proof/definition method: Compose the unconditional row/column
   symmetry equivalence with the preceding zero-row support theorem,
   using the standard propositional tauto tactic.
   Library reuse: indexed_basis_covariance_matrix_zero_row_iff_zero_column,
   indexed_basis_covariance_matrix_zero_row_iff_constant_on_support,
   Stdlib.Vectors.Vector.nth and standard tauto.
   Boundary: Finite support-constancy is not a full rank computation or
   an empirical claim about correlations between IQ subtests.
   *)
  Theorem indexed_basis_covariance_matrix_zero_column_iff_constant_on_support :
    forall basis (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall j : Fin.t (length basis),
          indexed_basis_cross_covariance_matrix basis basis j i = 0) <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           Vector.nth (Vector.of_list basis) i x = c).
  Proof.
    intros basis i Hmass Hw.
    pose proof
      (indexed_basis_covariance_matrix_zero_row_iff_zero_column
        basis i) as Hsym.
    pose proof
      (indexed_basis_covariance_matrix_zero_row_iff_constant_on_support
        basis i Hmass Hw) as Hrow.
    tauto.
  Qed.


  (**
   [indexed_basis_covariance_matrix_positive_diagonal_iff_nonconstant_on_support]
   (theorem) — Strict positive indexed variance iff the selected score
   is not constant on the finite positive-weight support.
   Mathematical meaning: Each covariance diagonal is positive
   precisely when no constant real value agrees with the selected
   score at every outcome carrying positive sample mass.
   Exact checked proposition: For any bounded basis index i under unit
   total mass and nonnegative sampled weights, 0 < covariance(i,i)
   iff not exists c:R with selected_score i x=c at every sampled x
   whose weight is strictly positive.
   Premises and side conditions: Zero-weight observations and repeated
   scores are allowed. No score independence or invertibility is assumed.
   Proof/definition method: Rewrite the indexed diagonal as scalar
   variance and invoke the existing strict-variance iff support theorem.
   Library reuse: indexed_basis_covariance_matrix_diagonal,
   variance_positive_iff_no_constant_on_positive_weight_support,
   Stdlib.Vectors.Vector.nth and Stdlib.Reals.
   Boundary: This gives finite-coordinate strict variance, not
   eigenvalue positivity or full matrix positive definiteness.
   *)
  Theorem indexed_basis_covariance_matrix_positive_diagonal_iff_nonconstant_on_support :
    forall basis (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < indexed_basis_cross_covariance_matrix basis basis i i <->
       ~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             Vector.nth (Vector.of_list basis) i x = c)).
  Proof.
    intros basis i Hmass Hw.
    rewrite indexed_basis_covariance_matrix_diagonal.
    apply variance_positive_iff_no_constant_on_positive_weight_support;
      assumption.
  Qed.

  (**
   [indexed_basis_covariance_matrix_nonzero_entry_implies_positive_diagonals]
   (theorem) — Any nonzero covariance entry has two positive variances.
   Mathematical meaning: Nonzero off-diagonal covariance is impossible
   when either of the corresponding basis scores has zero variance.
   Exact checked proposition: For bounded i and j, unit total mass,
   nonnegative sampled weights and indexed covariance(i,j) <> 0 imply
   0 < indexed covariance(i,i) and 0 < indexed covariance(j,j).
   Premises and side conditions: The indices may coincide; no
   independent-score hypothesis or positive-definite matrix is needed.
   Proof/definition method: Rewrite both diagonal cells as variances;
   unfold only the indexed cross-covariance entry in the premise and
   apply the existing scalar nonzero-covariance theorem.
   Library reuse: indexed_basis_covariance_matrix_diagonal,
   nonzero_covariance_implies_positive_variances, Stdlib.Vectors.Fin.
   Boundary: Positive diagonal cells alone do not imply full-rank
   covariance, matrix invertibility or statistical significance.
   *)
  Theorem indexed_basis_covariance_matrix_nonzero_entry_implies_positive_diagonals :
    forall basis (i j : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix basis basis i j <> 0 ->
      0 < indexed_basis_cross_covariance_matrix basis basis i i /\
      0 < indexed_basis_cross_covariance_matrix basis basis j j.
  Proof.
    intros basis i j Hmass Hw Hnonzero.
    rewrite !indexed_basis_covariance_matrix_diagonal.
    unfold indexed_basis_cross_covariance_matrix in Hnonzero.
    apply nonzero_covariance_implies_positive_variances; assumption.
  Qed.

  (**
   [indexed_basis_covariance_matrix_nonzero_entry_implies_nonconstant_scores]
   (theorem) — Nonzero covariance requires variation in both selected scores.
   Mathematical meaning: If two basis coordinates have nonzero covariance,
   neither score can be constant throughout the positive-weight support.
   Exact checked proposition: Under normalized nonnegative finite weights,
   indexed covariance(i,j) <> 0 implies no positive-support constant
   witness exists for either selected score i or selected score j.
   Premises and side conditions: There is no Gaussian model,
   independence assumption or requirement that the two scores differ;
   zero-weight samples need not have the same score values.
   Proof/definition method: Obtain both strictly positive diagonal
   entries from the existing nonzero-entry theorem, then convert each
   one to positive-support nonconstancy using the new diagonal iff.
   Library reuse: indexed_basis_covariance_matrix_nonzero_entry_implies_positive_diagonals,
   indexed_basis_covariance_matrix_positive_diagonal_iff_nonconstant_on_support
   and Stdlib.Reals/Vector.
   Boundary: This is a necessary condition for nonzero covariance,
   not an equivalence or an empirical correlation test.
   *)
  Theorem indexed_basis_covariance_matrix_nonzero_entry_implies_nonconstant_scores :
    forall basis (i j : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_cross_covariance_matrix basis basis i j <> 0 ->
      (~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             Vector.nth (Vector.of_list basis) i x = c)) /\
      (~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             Vector.nth (Vector.of_list basis) j x = c)).
  Proof.
    intros basis i j Hmass Hw Hnonzero.
    pose proof
      (indexed_basis_covariance_matrix_nonzero_entry_implies_positive_diagonals
        basis i j Hmass Hw Hnonzero) as [Hi Hj].
    split.
    - apply (proj1
        (indexed_basis_covariance_matrix_positive_diagonal_iff_nonconstant_on_support
          basis i Hmass Hw)); exact Hi.
    - apply (proj1
        (indexed_basis_covariance_matrix_positive_diagonal_iff_nonconstant_on_support
          basis j Hmass Hw)); exact Hj.
  Qed.

  (**
   [indexed_basis_covariance_two_coordinate_form] (definition) — The covariance quadratic form restricted to any two bounded basis coordinates with real coefficients a and b.
   Mathematical meaning: The covariance quadratic form restricted to any two bounded basis coordinates with real coefficients a and b.
   Exact declaration: The form is (a*a)*M(i,i)+(b*b)*M(j,j)+2*a*b*M(i,j), using the already established indexed covariance cells M.
   Premises and side conditions: Both indices are Fin.t (length basis). They may be equal; score lists may be empty or contain duplicates. No weight normalization or positivity premise is needed for the definition.
   Proof/definition method: Combine preexisting covariance entries with ordinary Stdlib.Reals arithmetic, without implementing matrix iteration or a second summation algorithm.
   Library reuse: indexed_basis_cross_covariance_matrix, Stdlib.Reals, Stdlib.Vectors.Fin and Vector.
   Boundary: This is a purpose-specific two-coordinate quadratic polynomial, not a generic matrix library, eigenvalue algorithm or a claim of strict positivity.
   *)
  Definition indexed_basis_covariance_two_coordinate_form
      (basis : list (Outcome -> R))
      (i j : Fin.t (length basis)) (a b : R) : R :=
    (a * a) * indexed_basis_cross_covariance_matrix basis basis i i +
    (b * b) * indexed_basis_cross_covariance_matrix basis basis j j +
    2 * a * b * indexed_basis_cross_covariance_matrix basis basis i j.

  (**
   [indexed_basis_covariance_two_coordinate_form_as_variance] (theorem) — The indexed two-coordinate covariance polynomial is exactly the variance of the corresponding weighted pair of scores.
   Mathematical meaning: The indexed two-coordinate covariance polynomial is exactly the variance of the corresponding weighted pair of scores.
   Exact checked proposition: For all basis, bounded i,j, and real a,b, indexed_basis_covariance_two_coordinate_form basis i j a b equals variance (fun x => a*selected_i x+b*selected_j x).
   Premises and side conditions: No unit-mass or nonnegative-weight assumption is needed for this algebraic identity. Indices and scores may be equal, and weights may be signed.
   Proof/definition method: Rewrite the existing scalar two-weighted-score variance formula, then unfold the indexed form and covariance definitions; finish by definitional equality.
   Library reuse: variance_of_two_weighted_scores, covariance, variance, Stdlib.Vectors.Vector.nth.
   Boundary: For signed or unnormalized finite weights, this equality alone gives no nonnegativity or generic spectral theorem.
   *)
  Theorem indexed_basis_covariance_two_coordinate_form_as_variance :
    forall basis (i j : Fin.t (length basis)) a b,
      indexed_basis_covariance_two_coordinate_form basis i j a b =
      variance (fun x =>
        a * Vector.nth (Vector.of_list basis) i x +
        b * Vector.nth (Vector.of_list basis) j x).
  Proof.
    intros basis i j a b.
    symmetry.
    rewrite (variance_of_two_weighted_scores
      (Vector.nth (Vector.of_list basis) i)
      (Vector.nth (Vector.of_list basis) j) a b).
    unfold indexed_basis_covariance_two_coordinate_form,
      indexed_basis_cross_covariance_matrix.
    reflexivity.
  Qed.


  (**
   [indexed_basis_covariance_two_coordinate_form_as_list_matrix]
   (theorem) — Exact compatibility with the preexisting finite matrix API.
   Mathematical meaning: The polynomial assembled from two bounded
   Fin.t-indexed covariance cells equals the matrix quadratic form
   of those same two selected scores in the established list matrix.
   Exact checked proposition: For all basis, i,j : Fin.t(length basis),
   a,b : R, indexed_basis_covariance_two_coordinate_form basis i j a b =
   matrix_quadratic_form [a;b] (basis_covariance_matrix [selected_i;selected_j]).
   Premises and side conditions: No normalization, nonnegativity,
   independence or positive-definiteness assumption is required.
   The indices may coincide and repeated basis functions are allowed.
   Proof/definition method: Rewrite the indexed form as scalar
   variance, use variance_extensional with the existing two-element
   linear_combination and Stdlib ring arithmetic, then apply the
   unconditional generic covariance_matrix_quadratic_form_is_variance
   theorem. Pair projections and mapped matrix entries are definitionally
   equal to the old list-matrix representation.
   Library reuse: indexed_basis_covariance_two_coordinate_form_as_variance,
   variance_extensional, linear_combination, FiniteSum.finite_sum,
   covariance_matrix_quadratic_form_is_variance_unconditional,
   matrix_quadratic_form, basis_covariance_matrix and Stdlib.List.
   Boundary: This connects two finite matrix representations;
   generic rank-nullity, determinants and Gaussian densities are unproved.
   *)
  Theorem indexed_basis_covariance_two_coordinate_form_as_list_matrix :
    forall basis (i j : Fin.t (length basis)) a b,
      indexed_basis_covariance_two_coordinate_form basis i j a b =
      matrix_quadratic_form [a; b]
        (basis_covariance_matrix
          [Vector.nth (Vector.of_list basis) i;
           Vector.nth (Vector.of_list basis) j]).
  Proof.
    intros basis i j a b.
    rewrite indexed_basis_covariance_two_coordinate_form_as_variance.
    set (f := Vector.nth (Vector.of_list basis) i).
    set (g := Vector.nth (Vector.of_list basis) j).
    transitivity (variance (linear_combination [(a, f); (b, g)])).
    - apply variance_extensional.
      intro x.
      unfold linear_combination, FiniteSum.finite_sum.
      simpl.
      ring.
    - symmetry.
      change
        (matrix_quadratic_form
           (map fst [(a, f); (b, g)])
           (covariance_matrix [(a, f); (b, g)]) =
         variance (linear_combination [(a, f); (b, g)])).
      apply covariance_matrix_quadratic_form_is_variance_unconditional.
  Qed.

  (**
   [indexed_basis_covariance_two_coordinate_form_nonnegative] (theorem) — Every two-coordinate principal covariance quadratic is nonnegative under normalized nonnegative finite weights.
   Mathematical meaning: Every two-coordinate principal covariance quadratic is nonnegative under normalized nonnegative finite weights.
   Exact checked proposition: For all basis, bounded i,j, and real a,b, total_mass=1 and sampled weights >=0 imply 0 <= indexed_basis_covariance_two_coordinate_form basis i j a b.
   Premises and side conditions: The coefficients can both be zero and indices can be repeated. No positive definiteness, distinctness or score independence is assumed.
   Proof/definition method: Rewrite the indexed two-coordinate form
   as a quadratic on the existing two-score list covariance matrix,
   then specialize the general finite fixed-basis covariance
   positive-semidefinite theorem with [a;b] and the selected scores.
   Library reuse: indexed_basis_covariance_two_coordinate_form_as_list_matrix,
   fixed_basis_covariance_matrix_positive_semidefinite, Stdlib.List and Reals.
   Boundary: The result covers every two-coordinate direction, not arbitrary-dimensional determinant, rank, or eigenvalue claims.
   *)
  Theorem indexed_basis_covariance_two_coordinate_form_nonnegative :
    forall basis (i j : Fin.t (length basis)) a b,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <= indexed_basis_covariance_two_coordinate_form basis i j a b.
  Proof.
    intros basis i j a b Hmass Hw.
    rewrite indexed_basis_covariance_two_coordinate_form_as_list_matrix.
    apply fixed_basis_covariance_matrix_positive_semidefinite.
    - reflexivity.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_two_coordinate_form_zero_iff_constant_on_support] (theorem) — The two-coordinate form vanishes exactly when the selected coefficient-weighted score pair is constant on positive-weight sample support.
   Mathematical meaning: The two-coordinate form vanishes exactly when the selected coefficient-weighted score pair is constant on positive-weight sample support.
   Exact checked proposition: Under unit mass and nonnegative sampled weights, form(basis,i,j,a,b)=0 iff some real c satisfies a*selected_i x+b*selected_j x=c at every sampled positive-weight x.
   Premises and side conditions: No coefficient is required to be nonzero; basis scores and indices may repeat. The support condition does not constrain zero-weight outcomes.
   Proof/definition method: Rewrite form to the existing variance expression, then reuse the checked variance_zero_iff_exists_constant_on_positive_weight_support theorem.
   Library reuse: indexed_basis_covariance_two_coordinate_form_as_variance, variance_zero_iff_exists_constant_on_positive_weight_support.
   Boundary: This is exact finite-sample support nullity, not a generic dimension-of-kernel or matrix-rank theorem.
   *)
  Theorem indexed_basis_covariance_two_coordinate_form_zero_iff_constant_on_support :
    forall basis (i j : Fin.t (length basis)) a b,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_two_coordinate_form basis i j a b = 0 <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           a * Vector.nth (Vector.of_list basis) i x +
           b * Vector.nth (Vector.of_list basis) j x = c).
  Proof.
    intros basis i j a b Hmass Hw.
    rewrite indexed_basis_covariance_two_coordinate_form_as_variance.
    apply variance_zero_iff_exists_constant_on_positive_weight_support;
      assumption.
  Qed.

  (**
   [indexed_basis_covariance_two_coordinate_form_positive_iff_nonconstant_on_support] (theorem) — A two-coordinate covariance quadratic is strictly positive exactly when its selected weighted pair is nonconstant on positive-weight finite support.
   Mathematical meaning: A two-coordinate covariance quadratic is strictly positive exactly when its selected weighted pair is nonconstant on positive-weight finite support.
   Exact checked proposition: Under unit mass and nonnegative sampled weights, 0<form(basis,i,j,a,b) iff there is no c agreeing with a*selected_i x+b*selected_j x at all sampled positive-weight x.
   Premises and side conditions: Zero coefficients, repeated indices and dependent basis scores are allowed; neither invertibility nor strict positivity of all directions is presumed.
   Proof/definition method: Rewrite the form to the existing two-score variance and invoke variance_positive_iff_no_constant_on_positive_weight_support.
   Library reuse: indexed_basis_covariance_two_coordinate_form_as_variance, variance_positive_iff_no_constant_on_positive_weight_support.
   Boundary: Strict positivity in this particular direction is not general positive definiteness or empirical statistical validity.
   *)
  Theorem indexed_basis_covariance_two_coordinate_form_positive_iff_nonconstant_on_support :
    forall basis (i j : Fin.t (length basis)) a b,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < indexed_basis_covariance_two_coordinate_form basis i j a b <->
       ~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             a * Vector.nth (Vector.of_list basis) i x +
             b * Vector.nth (Vector.of_list basis) j x = c)).
  Proof.
    intros basis i j a b Hmass Hw.
    rewrite indexed_basis_covariance_two_coordinate_form_as_variance.
    apply variance_positive_iff_no_constant_on_positive_weight_support;
      assumption.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_form] (definition) — A dimension-checked vector of coefficients applied to the existing covariance matrix of the same finite score basis.
   Mathematical meaning: A dimension-checked vector of coefficients applied to the existing covariance matrix of the same finite score basis.
   Exact declaration: For basis of length n and coefficients : Vector.t R n, the value is matrix_quadratic_form (Vector.to_list coefficients) (basis_covariance_matrix basis).
   Premises and side conditions: The vector length equals the score-basis length by its type; the score basis can be empty or repeated. Neither positive weights nor total-mass normalization is required to define the expression.
   Proof/definition method: Use the existing generic finite list-matrix quadratic and the standard library Vector.to_list conversion. No new finite sum, matrix index recursion or multiplication routine is introduced.
   Library reuse: Stdlib.Vectors.Vector.to_list and VectorSpec.length_to_list, matrix_quadratic_form, basis_covariance_matrix.
   Boundary: The coefficient type is fully dimension-safe, while the underlying matrix remains the previously certified list representation. This is not a determinant or spectral decomposition.
   *)
  Definition indexed_basis_covariance_quadratic_form
      (basis : list (Outcome -> R))
      (coefficients : Vector.t R (length basis)) : R :=
    matrix_quadratic_form (Vector.to_list coefficients)
      (basis_covariance_matrix basis).

  (**
   [indexed_basis_covariance_quadratic_as_variance] (theorem) — The arbitrary-dimensional bounded coefficient covariance quadratic equals the finite variance of its weighted basis score.
   Mathematical meaning: The arbitrary-dimensional bounded coefficient covariance quadratic equals the finite variance of its weighted basis score.
   Exact checked proposition: Under total_mass=1, indexed_basis_covariance_quadratic_form basis coefficients = variance (weighted_basis_sum (Vector.to_list coefficients) basis).
   Premises and side conditions: The basis is any finite score list and the coefficient vector has exactly its length by type; signed weights are allowed, but the existing compatible fixed-basis variance theorem explicitly assumes unit total sample mass.
   Proof/definition method: Unfold the new interface; apply the established fixed_basis_weighted_variance_identity in reverse. Discharge coefficient/basis length using the Stdlib VectorSpec.length_to_list theorem.
   Library reuse: fixed_basis_weighted_variance_identity and Stdlib.Vectors.VectorSpec.length_to_list.
   Boundary: This is a finite exact variance identity and does not assert Gaussianity, strict positivity or a generic matrix spectral representation.
   *)
  Theorem indexed_basis_covariance_quadratic_as_variance :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      indexed_basis_covariance_quadratic_form basis coefficients =
      variance (weighted_basis_sum
        (Vector.to_list coefficients) basis).
  Proof.
    intros basis coefficients Hmass.
    unfold indexed_basis_covariance_quadratic_form.
    symmetry.
    apply fixed_basis_weighted_variance_identity.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_nonnegative] (theorem) — Every compatible dimension-indexed coefficient direction has a nonnegative covariance quadratic under finite probability assumptions.
   Mathematical meaning: Every compatible dimension-indexed coefficient direction has a nonnegative covariance quadratic under finite probability assumptions.
   Exact checked proposition: For any basis and Vector.t R (length basis) coefficients, total_mass=1 and nonnegative sample weights imply 0 <= indexed_basis_covariance_quadratic_form basis coefficients.
   Premises and side conditions: The coefficient vector may be zero or the basis may be empty. Repeated or linearly dependent scores are allowed; strictly positive diagonals and invertibility are not required.
   Proof/definition method: Unfold the coefficient-vector interface, apply the earlier general fixed-basis positive-semidefinite theorem, and prove vector/list length equality using VectorSpec.length_to_list.
   Library reuse: fixed_basis_covariance_matrix_positive_semidefinite and Stdlib.Vectors.VectorSpec.length_to_list.
   Boundary: A positive-semidefinite finite covariance quadratic is not necessarily positive definite, invertible, or a certified generic rank-nullity computation.
   *)
  Theorem indexed_basis_covariance_quadratic_nonnegative :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      0 <= indexed_basis_covariance_quadratic_form basis coefficients.
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_covariance_matrix_positive_semidefinite.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_iff_constant_on_support] (theorem) — The bounded coefficient vector has a zero covariance quadratic exactly when its composite score is constant on positive-weight finite support.
   Mathematical meaning: The bounded coefficient vector has a zero covariance quadratic exactly when its composite score is constant on positive-weight finite support.
   Exact checked proposition: Under unit mass and nonnegative sample weights, indexed covariance quadratic = 0 iff there exists c:R such that weighted_basis_sum (Vector.to_list coefficients) basis x=c at each positive-weight sampled x.
   Premises and side conditions: The basis and coefficient lengths match by Vector.t typing; a zero coefficient direction, repeated basis functions, and zero-weight observations are all permitted.
   Proof/definition method: Unfold the vector coefficient interface and directly specialize the established fixed_basis_null_iff_exists_constant_on_positive_weight_support theorem, using the Stdlib vector-to-list length lemma.
   Library reuse: fixed_basis_null_iff_exists_constant_on_positive_weight_support and VectorSpec.length_to_list.
   Boundary: This characterizes support-wise kernel directions algebraically; it does not establish their dimension, rank, or empirical statistical independence.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_iff_constant_on_support :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_quadratic_form basis coefficients = 0 <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           weighted_basis_sum (Vector.to_list coefficients) basis x = c).
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_null_iff_exists_constant_on_positive_weight_support.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support] (theorem) — A bounded coefficient direction has strictly positive covariance quadratic precisely when no support-constant composite score exists.
   Mathematical meaning: A bounded coefficient direction has strictly positive covariance quadratic precisely when no support-constant composite score exists.
   Exact checked proposition: Under unit mass and nonnegative sampled weights, indexed covariance quadratic > 0 iff no c:R equals weighted_basis_sum (Vector.to_list coefficients) basis x at every positive-weight sampled x.
   Premises and side conditions: Dependent or repeated score functions can make some nonzero coefficient directions null; the theorem does not assume the covariance matrix is positive definite.
   Proof/definition method: Use the existing fixed-basis strict positivity iff positive-support nonconstancy theorem, discharging the only representation premise using VectorSpec.length_to_list.
   Library reuse: fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support and Stdlib.Vectors.VectorSpec.length_to_list.
   Boundary: Strict variance in one direction does not imply the matrix is invertible or that every direction is strictly positive.
   *)
  Theorem indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < indexed_basis_covariance_quadratic_form basis coefficients <->
       ~ (exists c : R,
           forall x, In x samples -> 0 < weight x ->
             weighted_basis_sum (Vector.to_list coefficients) basis x = c)).
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_positive_quadratic_iff_no_constant_on_positive_weight_support.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_basis] (theorem) — An indexed coefficient direction has zero covariance quadratic iff its composite score is uncorrelated with every score in the chosen finite basis.
   Mathematical meaning: An indexed coefficient direction has zero covariance quadratic iff its composite score is uncorrelated with every score in the chosen finite basis.
   Exact checked proposition: Under unit sample mass and nonnegative sampled weights, quadratic=0 iff forall g in basis, covariance (weighted_basis_sum (Vector.to_list coefficients) basis) g=0.
   Premises and side conditions: All finite basis score occurrences and compatible coefficient vector entries are included; zero weights or linear dependence are permitted. No distributional Gaussian assumption is added.
   Proof/definition method: Unfold the bounded coefficient interface, invoke the checked fixed_basis_null_iff_uncorrelated_with_basis theorem, and use VectorSpec.length_to_list instead of a custom list/vector length proof.
   Library reuse: fixed_basis_null_iff_uncorrelated_with_basis and Stdlib.Vectors.VectorSpec.length_to_list.
   Boundary: This exact orthogonality equivalence is coordinatewise; it does not compute a rank, basis for the kernel or continuous covariance operator.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_basis :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_quadratic_form basis coefficients = 0 <->
       forall g, In g basis ->
         covariance (weighted_basis_sum
           (Vector.to_list coefficients) basis) g = 0).
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_null_iff_uncorrelated_with_basis.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots] (theorem) — A dimension-safe coefficient direction is null iff its dot product with every existing covariance-matrix row is zero.
   Mathematical meaning: A dimension-safe coefficient direction is null iff its dot product with every existing covariance-matrix row is zero.
   Exact checked proposition: Under normalized nonnegative finite weights, quadratic=0 iff forall row in basis_covariance_matrix basis, vector_dot (Vector.to_list coefficients) row=0.
   Premises and side conditions: The length of the coefficient vector matches basis length by its type; no basis invertibility or rank premise is required, and empty bases are supported.
   Proof/definition method: Specialize the previously proven fixed_basis_null_iff_zero_dot_with_every_covariance_row with the standard Vector.to_list length theorem, without custom matrix row traversal.
   Library reuse: fixed_basis_null_iff_zero_dot_with_every_covariance_row, matrix_quadratic_form and VectorSpec.length_to_list.
   Boundary: The result gives an exact linear-equation characterization of the finite quadratic nullspace but not its cardinality or dimension.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_quadratic_form basis coefficients = 0 <->
       forall row, In row (basis_covariance_matrix basis) ->
         vector_dot (Vector.to_list coefficients) row = 0).
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_null_iff_zero_dot_with_every_covariance_row.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score] (theorem) — The variance-null coefficient direction is uncorrelated with every outcome score, not merely those listed in its basis.
   Mathematical meaning: The variance-null coefficient direction is uncorrelated with every outcome score, not merely those listed in its basis.
   Exact checked proposition: With total_mass=1 and nonnegative sampled weights, the bounded coefficient quadratic equals zero iff forall g : Outcome -> R, covariance (weighted_basis_sum (Vector.to_list coefficients) basis) g = 0.
   Premises and side conditions: The coefficient-vector length equals the basis length by its Vector.t type. All outcomes and score functions remain finite-sample weighted; no Gaussianity or independence assumption is made.
   Proof/definition method: Unfold the dimension-safe coefficient interface and apply the existing all-scores orthogonality iff for fixed finite bases, discharging the only length premise with VectorSpec.length_to_list.
   Library reuse: fixed_basis_null_iff_orthogonal_to_every_score, Stdlib.Vectors.VectorSpec.length_to_list and the established covariance definition.
   Boundary: Universal covariance nullity under a finite weighted sample is a stronger functional statement than vanishing selected rows, but does not compute a numerical kernel rank.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_quadratic_form basis coefficients = 0 <->
       forall g : Outcome -> R,
         covariance
           (weighted_basis_sum (Vector.to_list coefficients) basis) g = 0).
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_null_iff_orthogonal_to_every_score.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_positive_iff_not_uncorrelated_with_basis] (theorem) — Strictly positive coefficient-vector covariance curvature is equivalent to the failure of orthogonality to all basis scores.
   Mathematical meaning: Strictly positive coefficient-vector covariance curvature is equivalent to the failure of orthogonality to all basis scores.
   Exact checked proposition: For normalized nonnegative sample weights, 0 < indexed_basis_covariance_quadratic_form basis coefficients iff not(forall g in basis, covariance (weighted_basis_sum (Vector.to_list coefficients) basis) g = 0).
   Premises and side conditions: Zero-weight sample occurrences and linear dependence remain allowed; no additional positive-definite assumption is introduced. The chosen score basis may be empty.
   Proof/definition method: Instantiate the established fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis theorem after unfolding the representation and invoke the Stdlib vector/list length result.
   Library reuse: fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis, VectorSpec.length_to_list and the existing finite covariance algebra.
   Boundary: This is a strict-positivity criterion for one direction; it does not prove a nonsingular covariance matrix in every coefficient direction.
   *)
  Theorem indexed_basis_covariance_quadratic_positive_iff_not_uncorrelated_with_basis :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < indexed_basis_covariance_quadratic_form basis coefficients <->
       ~ (forall g, In g basis ->
           covariance (weighted_basis_sum
             (Vector.to_list coefficients) basis) g = 0)).
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_positive_quadratic_iff_not_uncorrelated_with_basis.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_positive_iff_nonzero_matrix_row_dot] (theorem) — Strict positivity of the typed coefficient covariance quadratic is exactly failure of all covariance row dot products to vanish.
   Mathematical meaning: Strict positivity of the typed coefficient covariance quadratic is exactly failure of all covariance row dot products to vanish.
   Exact checked proposition: For normalized nonnegative sample weights, 0 < indexed covariance quadratic iff not(forall row in basis_covariance_matrix basis, vector_dot (Vector.to_list coefficients) row = 0).
   Premises and side conditions: The vector length agrees by its type with basis length. The basis may be linearly dependent or empty; no invertibility, rank or nonzero sample-weight requirement beyond nonnegativity is added.
   Proof/definition method: Unfold the coefficient-vector quadratic and reuse the general list-matrix fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot result; provide its sole length witness via VectorSpec.length_to_list.
   Library reuse: fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot, VectorSpec.length_to_list, matrix_quadratic_form and vector_dot.
   Boundary: The result is an exact algebraic criterion, not an effective algorithm deciding nonzero real matrix rows or extracting a nullspace basis.
   *)
  Theorem indexed_basis_covariance_quadratic_positive_iff_nonzero_matrix_row_dot :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < indexed_basis_covariance_quadratic_form basis coefficients <->
       ~ (forall row, In row (basis_covariance_matrix basis) ->
           vector_dot (Vector.to_list coefficients) row = 0)).
  Proof.
    intros basis coefficients Hmass Hw.
    unfold indexed_basis_covariance_quadratic_form.
    apply fixed_basis_positive_quadratic_iff_nonzero_covariance_row_dot.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_matrix_row_dots_iff_constant_on_support] (theorem) — Every covariance row dot product vanishes exactly when the composite score is constant throughout positive-weight sample support.
   Mathematical meaning: Every covariance row dot product vanishes exactly when the composite score is constant throughout positive-weight sample support.
   Exact checked proposition: Under total_mass=1 and nonnegative sampled weights, (forall covariance row, vector_dot (Vector.to_list coefficients) row = 0) iff exists c:R, forall sampled x with positive weight, weighted_basis_sum (Vector.to_list coefficients) basis x = c.
   Premises and side conditions: No basis independence or invertibility is assumed. The zero-weight part of the sampled list is allowed to contain arbitrary score values.
   Proof/definition method: Directly invoke the established fixed_basis_zero_covariance_row_dots_iff_supported_constant theorem on the standard vector-to-list coefficient projection; use the library vector length lemma.
   Library reuse: fixed_basis_zero_covariance_row_dots_iff_supported_constant and Stdlib.Vectors.VectorSpec.length_to_list.
   Boundary: The equivalence describes exact real-valued finite support nullity without determining a linear subspace dimension or rank.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_matrix_row_dots_iff_constant_on_support :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall row, In row (basis_covariance_matrix basis) ->
          vector_dot (Vector.to_list coefficients) row = 0) <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           weighted_basis_sum (Vector.to_list coefficients) basis x = c).
  Proof.
    intros basis coefficients Hmass Hw.
    apply fixed_basis_zero_covariance_row_dots_iff_supported_constant.
    - apply VectorSpec.length_to_list.
    - exact Hmass.
    - exact Hw.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_nonzero_covariance_implies_positive] (theorem) — One nonzero covariance witness between the composite basis score and an arbitrary score certifies strict positivity of the typed coefficient quadratic.
   Mathematical meaning: One nonzero covariance witness between the composite basis score and an arbitrary score certifies strict positivity of the typed coefficient quadratic.
   Exact checked proposition: For normalized nonnegative finite weights, if covariance (weighted_basis_sum (Vector.to_list coefficients) basis) g <> 0 for some score g, then 0 < indexed_basis_covariance_quadratic_form basis coefficients.
   Premises and side conditions: The arbitrary comparison score need not belong to the basis; no empirical probability model, score independence or matrix invertibility is required. The witness must have nonzero covariance in the same normalized finite sample.
   Proof/definition method: Apply the earlier scalar nonzero_covariance_implies_positive_variances theorem to the composite score and g, then rewrite the bounded quadratic by the checked composite-score variance bridge.
   Library reuse: nonzero_covariance_implies_positive_variances, indexed_basis_covariance_quadratic_as_variance and Stdlib.Vectors.Vector.to_list.
   Boundary: A nonzero covariance witness is sufficient for positivity but does not establish a uniform bound or positive definiteness of all coefficient directions.
   *)
  Theorem indexed_basis_covariance_quadratic_nonzero_covariance_implies_positive :
    forall basis (coefficients : Vector.t R (length basis))
           (g : Outcome -> R),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      covariance (weighted_basis_sum
        (Vector.to_list coefficients) basis) g <> 0 ->
      0 < indexed_basis_covariance_quadratic_form basis coefficients.
  Proof.
    intros basis coefficients g Hmass Hw Hnonzero.
    pose proof
      (nonzero_covariance_implies_positive_variances
        (weighted_basis_sum (Vector.to_list coefficients) basis)
        g Hmass Hw Hnonzero) as [Hpositive _].
    rewrite (indexed_basis_covariance_quadratic_as_variance
      basis coefficients Hmass).
    exact Hpositive.
  Qed.

  (**
   [indexed_basis_covariance_two_coordinate_form_swap] (theorem) — Interchanging the two selected scores and their coefficients leaves the same two-coordinate finite covariance quadratic.
   Mathematical meaning: Interchanging the two selected scores and their coefficients leaves the same two-coordinate finite covariance quadratic.
   Exact checked proposition: For basis, bounded indices i and j, and reals a,b, indexed_basis_covariance_two_coordinate_form basis i j a b = indexed_basis_covariance_two_coordinate_form basis j i b a.
   Premises and side conditions: The scores and indices may coincide; there is no sample normalization, weight positivity, or covariance invertibility assumption. This is a purely algebraic covariance symmetry.
   Proof/definition method: Unfold the existing two-coordinate polynomial, rewrite only the reversed covariance entry using indexed_basis_covariance_matrix_symmetric, and finish with the Stdlib ring tactic.
   Library reuse: indexed_basis_covariance_matrix_symmetric, indexed_basis_covariance_two_coordinate_form, Stdlib.Reals and the ring tactic.
   Boundary: This states permutation invariance of a two-score form, not general invariance of arbitrary matrix factorization or basis transformations.
   *)
  Theorem indexed_basis_covariance_two_coordinate_form_swap :
    forall basis (i j : Fin.t (length basis)) a b,
      indexed_basis_covariance_two_coordinate_form basis i j a b =
      indexed_basis_covariance_two_coordinate_form basis j i b a.
  Proof.
    intros basis i j a b.
    unfold indexed_basis_covariance_two_coordinate_form.
    rewrite (indexed_basis_covariance_matrix_symmetric basis j i).
    ring.
  Qed.

  (**
   [indexed_basis_covariance_two_coordinate_form_homogeneous] (theorem) — The two-coordinate covariance polynomial is homogeneous of degree two in its real score coefficients.
   Mathematical meaning: The two-coordinate covariance polynomial is homogeneous of degree two in its real score coefficients.
   Exact checked proposition: For any real multiplier t, indexed_basis_covariance_two_coordinate_form basis i j (t*a) (t*b) = (t*t) * indexed_basis_covariance_two_coordinate_form basis i j a b.
   Premises and side conditions: Both indices are bounded by Fin.t. The sample weights can be signed or unnormalized, and no covariance positive-definiteness or Gaussian model is assumed.
   Proof/definition method: Unfold the original two-coordinate polynomial and use the maintained real polynomial ring normalization tactic. No new variance scaling lemma or matrix multiplication is implemented.
   Library reuse: indexed_basis_covariance_two_coordinate_form, Stdlib.Reals and standard ring normalization.
   Boundary: Degree-two coefficient homogeneity is algebraic and does not prove a spectral decomposition or positive variance without normalized nonnegative weights.
   *)
  Theorem indexed_basis_covariance_two_coordinate_form_homogeneous :
    forall basis (i j : Fin.t (length basis)) a b t,
      indexed_basis_covariance_two_coordinate_form
        basis i j (t * a) (t * b) =
      (t * t) *
        indexed_basis_covariance_two_coordinate_form basis i j a b.
  Proof.
    intros basis i j a b t.
    unfold indexed_basis_covariance_two_coordinate_form.
    ring.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_implies_bounded_row_dot_zero] (theorem) — A null arbitrary-dimensional coefficient vector has zero dot product against each total Fin.t-bounded covariance row.
   Mathematical meaning: A null arbitrary-dimensional coefficient vector has zero dot product against each total Fin.t-bounded covariance row.
   Exact checked proposition: For basis, coefficients : Vector.t R (length basis), and i : Fin.t (length basis), normalized nonnegative sample weights and indexed quadratic=0 imply that vector_dot (Vector.to_list coefficients) (map (fun g => covariance (Vector.nth (Vector.of_list basis) i) g) basis)=0.
   Premises and side conditions: The coefficient vector, row and basis dimensions match through Vec/Fin types. Duplicate scores, zero-weight outcomes and dependent bases are permitted.
   Proof/definition method: Use the existing zero-quadratic iff every list covariance row dot vanishes, then prove the selected bounded row occurs in the existing list covariance matrix using the previous indexed_basis_cross_covariance_matrix_row bridge and Stdlib.List.nth_error_In.
   Library reuse: indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots, indexed_basis_cross_covariance_matrix_row, basis_covariance_matrix_as_cross and Stdlib.List.nth_error_In.
   Boundary: This is one direction of an indexed matrix kernel characterization; surjectivity of Fin indices over arbitrary list rows is not asserted here, and rank/nullity dimensions remain separate.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_implies_bounded_row_dot_zero :
    forall basis (coefficients : Vector.t R (length basis))
           (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_covariance_quadratic_form basis coefficients = 0 ->
      vector_dot (Vector.to_list coefficients)
        (map (fun g => covariance
          (Vector.nth (Vector.of_list basis) i) g) basis) = 0.
  Proof.
    intros basis coefficients i Hmass Hw Hzero.
    pose proof
      (proj1 (indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots
        basis coefficients Hmass Hw) Hzero) as Hrows.
    apply Hrows.
    eapply nth_error_In.
    rewrite basis_covariance_matrix_as_cross.
    apply indexed_basis_cross_covariance_matrix_row.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_implies_uncorrelated_indexed_score] (theorem) — An arbitrary-dimensional null coefficient direction is uncorrelated with every single Fin.t-selected basis score.
   Mathematical meaning: An arbitrary-dimensional null coefficient direction is uncorrelated with every single Fin.t-selected basis score.
   Exact checked proposition: For any basis, vector coefficients and bounded i, unit-mass nonnegative sampled weights and indexed quadratic=0 imply covariance (weighted_basis_sum (Vector.to_list coefficients) basis) (Vector.nth (Vector.of_list basis) i)=0.
   Premises and side conditions: The finite basis may be empty, in which case there is no bounded index to select. No independent-score, nonzero-direction or positive-definiteness assumption is required.
   Proof/definition method: Specialize the previously verified nullity iff covariance vanishes against every arbitrary comparison score to the bounded score obtained by Stdlib Vector.nth.
   Library reuse: indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score and Stdlib.Vectors.Vector.nth.
   Boundary: This is an exact finite covariance coordinate implication, not an estimate of correlations, a generic rank identity or an assertion about continuous random variables.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_implies_uncorrelated_indexed_score :
    forall basis (coefficients : Vector.t R (length basis))
           (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      indexed_basis_covariance_quadratic_form basis coefficients = 0 ->
      covariance
        (weighted_basis_sum (Vector.to_list coefficients) basis)
        (Vector.nth (Vector.of_list basis) i) = 0.
  Proof.
    intros basis coefficients i Hmass Hw Hzero.
    apply (proj1
      (indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score
        basis coefficients Hmass Hw) Hzero).
  Qed.

  (**
   [indexed_basis_covariance_quadratic_nonzero_indexed_covariance_implies_positive] (theorem) — A nonzero covariance between the weighted basis composite and any bounded basis score witnesses strictly positive variance in its coefficient direction.
   Mathematical meaning: A nonzero covariance between the weighted basis composite and any bounded basis score witnesses strictly positive variance in its coefficient direction.
   Exact checked proposition: If total_mass=1, sample weights are nonnegative and covariance (weighted_basis_sum (Vector.to_list coefficients) basis) (Vector.nth (Vector.of_list basis) i) <> 0, then indexed_basis_covariance_quadratic_form basis coefficients > 0.
   Premises and side conditions: No positive definiteness, statistical independence or nonzero variance of every basis coordinate is assumed. The bounded score and composite use the identical finite sample.
   Proof/definition method: Specialize the already checked nonzero-covariance-witness-implies-positive indexed quadratic theorem to the score selected by Stdlib.Vectors.Vector.nth.
   Library reuse: indexed_basis_covariance_quadratic_nonzero_covariance_implies_positive and Stdlib.Vectors.Fin/Vector.
   Boundary: Only the direction with a witnessed nonzero covariance is certified positive; a claim about invertibility, generic matrix ranks or empirical IQ correlations would require separate proofs.
   *)
  Theorem indexed_basis_covariance_quadratic_nonzero_indexed_covariance_implies_positive :
    forall basis (coefficients : Vector.t R (length basis))
           (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      covariance
        (weighted_basis_sum (Vector.to_list coefficients) basis)
        (Vector.nth (Vector.of_list basis) i) <> 0 ->
      0 < indexed_basis_covariance_quadratic_form basis coefficients.
  Proof.
    intros basis coefficients i Hmass Hw Hnonzero.
    apply (indexed_basis_covariance_quadratic_nonzero_covariance_implies_positive
      basis coefficients
      (Vector.nth (Vector.of_list basis) i) Hmass Hw).
    exact Hnonzero.
  Qed.

  (**
   [indexed_basis_covariance_matrix_row_has_bounded_index] (theorem) — Every row appearing in the previously constructed list covariance matrix is the row selected by some valid Fin.t basis index.
   Mathematical meaning: Every row appearing in the previously constructed list covariance matrix is the row selected by some valid Fin.t basis index.
   Exact checked proposition: For any basis and row with In row (basis_covariance_matrix basis), there exists i : Fin.t (length basis) such that row = map (fun g => covariance (Vector.nth (Vector.of_list basis) i) g) basis.
   Premises and side conditions: The basis may contain duplicate scores or be empty; membership of the row supplies the only existence hypothesis. No assumptions on sample weight sign, total mass, Gaussianity, invertibility, or scores are needed.
   Proof/definition method: Use Stdlib.List.In_nth_error to obtain a row position; Stdlib.List.nth_error_Some and length_map establish the bound. Convert the position to a maintained Fin.t using Fin.of_nat_lt and Fin.to_nat_of_nat, then identify the row via the already certified indexed_basis_cross_covariance_matrix_row theorem.
   Library reuse: Stdlib.List.In_nth_error, nth_error_Some, length_map, Stdlib.Vectors.Fin.of_nat_lt and Fin.to_nat_of_nat, indexed_basis_cross_covariance_matrix_row, basis_covariance_matrix_as_cross.
   Boundary: This proves every matrix row is represented by some bounded index, including duplicate rows; it does not assert uniqueness or compute a rank or eigenvalue.
   *)
  Theorem indexed_basis_covariance_matrix_row_has_bounded_index :
    forall basis row,
      In row (basis_covariance_matrix basis) ->
      exists i : Fin.t (length basis),
        row = map (fun g => covariance
          (Vector.nth (Vector.of_list basis) i) g) basis.
  Proof.
    intros basis row Hrow.
    destruct (In_nth_error (basis_covariance_matrix basis) row Hrow)
      as [n Hnth].
    assert (Hlen : length (basis_covariance_matrix basis) =
                   length basis).
    { unfold basis_covariance_matrix.
      rewrite length_map.
      reflexivity. }
    assert (Hbound : (n < length basis)%nat).
    { rewrite <- Hlen.
      apply (proj1 (nth_error_Some _ _)).
      rewrite Hnth.
      discriminate. }
    exists (Fin.of_nat_lt Hbound).
    pose proof
      (indexed_basis_cross_covariance_matrix_row
        basis basis (Fin.of_nat_lt Hbound)) as Hselected.
    rewrite <- basis_covariance_matrix_as_cross in Hselected.
    rewrite Fin.to_nat_of_nat in Hselected.
    simpl in Hselected.
    rewrite Hnth in Hselected.
    inversion Hselected.
    reflexivity.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero] (theorem) — The general typed coefficient covariance quadratic vanishes exactly when it annihilates every Fin.t-indexed basis covariance row.
   Mathematical meaning: The general typed coefficient covariance quadratic vanishes exactly when it annihilates every Fin.t-indexed basis covariance row.
   Exact checked proposition: Under unit mass and nonnegative sampled weights, indexed_basis_covariance_quadratic_form basis coefficients = 0 iff for every i:Fin.t(length basis), vector_dot (Vector.to_list coefficients) (map (fun g => covariance (Vector.nth (Vector.of_list basis) i) g) basis)=0.
   Premises and side conditions: All indices and coefficient lengths are bounded by the standard library vector types. Zero weights, repeated scores and linearly dependent bases remain permitted; Gaussian and matrix invertibility assumptions are absent.
   Proof/definition method: Use the already proven zero-quadratic-to-bounded-row direction. Conversely, use the generic list-matrix zero-row-dot iff, and apply the new list-row-surjectivity theorem to reify an index for each row that appears in the matrix.
   Library reuse: indexed_basis_covariance_quadratic_zero_implies_bounded_row_dot_zero, indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots and indexed_basis_covariance_matrix_row_has_bounded_index.
   Boundary: This is a full finite coordinatewise kernel criterion, but it does not calculate the dimension, nullity or basis of that kernel.
   *)
  Theorem indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_quadratic_form basis coefficients = 0 <->
       forall i : Fin.t (length basis),
         vector_dot (Vector.to_list coefficients)
           (map (fun g => covariance
             (Vector.nth (Vector.of_list basis) i) g) basis) = 0).
  Proof.
    intros basis coefficients Hmass Hw.
    split.
    - intros Hzero i.
      apply indexed_basis_covariance_quadratic_zero_implies_bounded_row_dot_zero;
        assumption.
    - intro Hbounded.
      apply (proj2
        (indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots
          basis coefficients Hmass Hw)).
      intros row Hrow.
      destruct (indexed_basis_covariance_matrix_row_has_bounded_index
        basis row Hrow) as [i Hselected].
      subst row.
      apply Hbounded.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot] (theorem) — A dimension-safe coefficient covariance quadratic is positive precisely when the indexed covariance row dot products do not all vanish.
   Mathematical meaning: A dimension-safe coefficient covariance quadratic is positive precisely when the indexed covariance row dot products do not all vanish.
   Exact checked proposition: Under total_mass=1 and nonnegative sample weights, 0 < indexed_basis_covariance_quadratic_form basis coefficients iff not (forall i : Fin.t (length basis), vector_dot (Vector.to_list coefficients) (map (fun g => covariance selected_i g) basis)=0).
   Premises and side conditions: All coefficient and row dimensions are enforced by Vector.t and Fin.t. The basis may be repeated or linearly dependent, and no invertibility or Gaussianity is assumed.
   Proof/definition method: Combine three previously checked iff theorems: positive iff not all existing matrix-row dots vanish, zero quadratic iff all existing matrix-row dots vanish, and zero quadratic iff all bounded row dots vanish. The standard tauto tactic composes them without a new real inequality proof.
   Library reuse: indexed_basis_covariance_quadratic_positive_iff_nonzero_matrix_row_dot, indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots, indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero, Stdlib.tauto.
   Boundary: A negated universal indexed-row condition witnesses strict positive curvature logically; no finite matrix rank or nonzero-row extraction algorithm is claimed.
   *)
  Theorem indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (0 < indexed_basis_covariance_quadratic_form basis coefficients <->
       ~ (forall i : Fin.t (length basis),
            vector_dot (Vector.to_list coefficients)
              (map (fun g => covariance
                (Vector.nth (Vector.of_list basis) i) g) basis) = 0)).
  Proof.
    intros basis coefficients Hmass Hw.
    pose proof
      (indexed_basis_covariance_quadratic_positive_iff_nonzero_matrix_row_dot
        basis coefficients Hmass Hw) as Hpositive.
    pose proof
      (indexed_basis_covariance_quadratic_zero_iff_zero_matrix_row_dots
        basis coefficients Hmass Hw) as Hlist.
    pose proof
      (indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero
        basis coefficients Hmass Hw) as Hindexed.
    tauto.
  Qed.

  (**
   [indexed_basis_covariance_bounded_row_dots_zero_iff_constant_on_support] (theorem) — All bounded covariance row dot products vanish precisely when the coefficient-weighted composite score is constant on positive-weight finite support.
   Mathematical meaning: All bounded covariance row dot products vanish precisely when the coefficient-weighted composite score is constant on positive-weight finite support.
   Exact checked proposition: For normalized nonnegative sample weights, (forall bounded i, vector_dot coefficient_list (map (fun g => covariance selected_i g) basis)=0) iff exists c:R such that weighted_basis_sum coefficient_list basis x=c at every sampled x with positive weight.
   Premises and side conditions: The coefficient vector has exactly the basis length. Scores and sample occurrences may repeat, and zero-weight outcomes need not satisfy the supported-constant equality.
   Proof/definition method: Compose the new full indexed-row zero-quadratic iff with the already checked finite positive-support zero-quadratic iff, using standard tauto.
   Library reuse: indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero, indexed_basis_covariance_quadratic_zero_iff_constant_on_support and Stdlib.tauto.
   Boundary: This characterizes finite weighted row-kernel directions exactly, but does not compute their dimension or claim anything about continuous probability.
   *)
  Theorem indexed_basis_covariance_bounded_row_dots_zero_iff_constant_on_support :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall i : Fin.t (length basis),
          vector_dot (Vector.to_list coefficients)
            (map (fun g => covariance
              (Vector.nth (Vector.of_list basis) i) g) basis) = 0) <->
       exists c : R,
         forall x, In x samples -> 0 < weight x ->
           weighted_basis_sum (Vector.to_list coefficients) basis x = c).
  Proof.
    intros basis coefficients Hmass Hw.
    pose proof
      (indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero
        basis coefficients Hmass Hw) as Hindexed.
    pose proof
      (indexed_basis_covariance_quadratic_zero_iff_constant_on_support
        basis coefficients Hmass Hw) as Hsupported.
    tauto.
  Qed.

  (**
   [indexed_basis_covariance_bounded_row_dots_zero_iff_uncorrelated_with_every_score] (theorem) — Annihilating all Fin.t-indexed covariance rows is equivalent to the composite score being uncorrelated with every outcome score.
   Mathematical meaning: Annihilating all Fin.t-indexed covariance rows is equivalent to the composite score being uncorrelated with every outcome score.
   Exact checked proposition: Under mass-one nonnegative weights, all bounded covariance row dots vanish iff forall g : Outcome -> R, covariance (weighted_basis_sum (Vector.to_list coefficients) basis) g = 0.
   Premises and side conditions: All indices and vector coefficient dimensions are statically bounded. No basis independence or nonzero variance premise is made, and finite samples with duplicates are permitted.
   Proof/definition method: Compose the established indexed bounded-row zero-quadratic equivalence with the stronger checked zero-quadratic iff all-scores covariance orthogonality result by Stdlib.tauto.
   Library reuse: indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero, indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score and Stdlib.tauto.
   Boundary: This exact finite-sample orthogonality criterion is not the dimension of a matrix kernel or a Gaussian conditional independence assertion.
   *)
  Theorem indexed_basis_covariance_bounded_row_dots_zero_iff_uncorrelated_with_every_score :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      ((forall i : Fin.t (length basis),
          vector_dot (Vector.to_list coefficients)
            (map (fun g => covariance
              (Vector.nth (Vector.of_list basis) i) g) basis) = 0) <->
       forall g : Outcome -> R,
         covariance
           (weighted_basis_sum (Vector.to_list coefficients) basis) g = 0).
  Proof.
    intros basis coefficients Hmass Hw.
    pose proof
      (indexed_basis_covariance_quadratic_zero_iff_bounded_row_dots_zero
        basis coefficients Hmass Hw) as Hindexed.
    pose proof
      (indexed_basis_covariance_quadratic_zero_iff_uncorrelated_with_every_score
        basis coefficients Hmass Hw) as Hall.
    tauto.
  Qed.

  (**
   [indexed_basis_covariance_positive_definite] (definition) — A type-checked positive-definiteness predicate for all nonzero real coefficient vectors of a finite basis.
   Mathematical meaning: A type-checked positive-definiteness predicate for all nonzero real coefficient vectors of a finite basis.
   Exact declaration: indexed_basis_covariance_positive_definite basis means forall coefficients : Vector.t R (length basis), Vector.to_list coefficients <> repeat 0 (length basis) -> 0 < indexed_basis_covariance_quadratic_form basis coefficients.
   Premises and side conditions: The coefficient shape is fixed by the basis dimension, and nonzeroness is stated using the existing list representation and Stdlib.List.repeat. No normalized weights are necessary to form the predicate.
   Proof/definition method: Define a transparent Prop abbreviation over the previously checked indexed coefficient quadratic and the standard Vector.to_list/List.repeat zero comparison, without defining an alternative vector zero test.
   Library reuse: indexed_basis_covariance_quadratic_form, Stdlib.Vectors.Vector.to_list, Stdlib.List.repeat and Stdlib.Reals.
   Boundary: This is the standard algebraic notion of strict positivity for all nonzero coefficient directions; it does not automatically hold for dependent bases or calculate eigenvalues.
   *)
  Definition indexed_basis_covariance_positive_definite
      (basis : list (Outcome -> R)) : Prop :=
    forall coefficients : Vector.t R (length basis),
      Vector.to_list coefficients <> repeat 0 (length basis) ->
      0 < indexed_basis_covariance_quadratic_form basis coefficients.

  (**
   [indexed_basis_covariance_positive_definite_iff_no_nonzero_supported_constant] (theorem) — A finite indexed covariance basis is positive definite precisely when no nonzero bounded coefficient vector forms a score constant on positive-weight support.
   Mathematical meaning: A finite indexed covariance basis is positive definite precisely when no nonzero bounded coefficient vector forms a score constant on positive-weight support.
   Exact checked proposition: Under total_mass=1 and nonnegative sampled weights, indexed_basis_covariance_positive_definite basis iff for every coefficients:Vector.t R (length basis) with Vector.to_list coefficients <> repeat 0 (length basis), no c:R is equal to its composite score on all positive-weight sampled outcomes.
   Premises and side conditions: Empty bases and zero-weight sample occurrences are allowed; the theorem does not require independent basis scores because that is captured by the no-constant-direction condition itself.
   Proof/definition method: Unfold the typed predicate and apply the previously verified pointwise indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support theorem in both directions.
   Library reuse: indexed_basis_covariance_positive_definite, indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support, Stdlib.Vectors.Vector.to_list and Stdlib.List.repeat.
   Boundary: This is a checked structural characterization of positive definiteness, not a numerical eigenvalue bound, finite-sample IQ data result or determinant formula.
   *)
  Theorem indexed_basis_covariance_positive_definite_iff_no_nonzero_supported_constant :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_positive_definite basis <->
       forall coefficients : Vector.t R (length basis),
         Vector.to_list coefficients <> repeat 0 (length basis) ->
         ~ (exists c : R,
             forall x, In x samples -> 0 < weight x ->
               weighted_basis_sum (Vector.to_list coefficients)
                 basis x = c)).
  Proof.
    intros basis Hmass Hw.
    unfold indexed_basis_covariance_positive_definite.
    split; intros Hproperty coefficients Hnonzero.
    - apply (proj1
        (indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support
          basis coefficients Hmass Hw)).
      apply Hproperty; exact Hnonzero.
    - apply (proj2
        (indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support
          basis coefficients Hmass Hw)).
      apply Hproperty; exact Hnonzero.
  Qed.

  (**
   [indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel] (theorem) — Positive definiteness is equivalent to the absence of nonzero typed coefficient vectors annihilating all bounded covariance rows.
   Mathematical meaning: Positive definiteness is equivalent to the absence of nonzero typed coefficient vectors annihilating all bounded covariance rows.
   Exact checked proposition: With normalized nonnegative weights, indexed_basis_covariance_positive_definite basis iff every coefficients:Vector.t R (length basis) with nonzero Vector.to_list has not(forall i:Fin.t(length basis), vector_dot coefficient_list (map (fun g => covariance selected_i g) basis)=0).
   Premises and side conditions: The basis may be dependent; in that case the no-nonzero-kernel condition can fail. All coefficient and row lengths are certified by standard vector types, and no Gaussian distribution is assumed.
   Proof/definition method: Unfold indexed positive definiteness and specialize the previously checked strictly-positive-quadratic iff nonzero bounded row dot theorem to each nonzero coefficient vector, in both directions.
   Library reuse: indexed_basis_covariance_positive_definite, indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot, Stdlib.Vectors.Fin/Vector.
   Boundary: This establishes a kernel-triviality criterion by exact finite covariance algebra, but does not compute matrix rank, eigenvalues or a nullspace basis.
   *)
  Theorem indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_positive_definite basis <->
       forall coefficients : Vector.t R (length basis),
         Vector.to_list coefficients <> repeat 0 (length basis) ->
         ~ (forall i : Fin.t (length basis),
              vector_dot (Vector.to_list coefficients)
                (map (fun g => covariance
                  (Vector.nth (Vector.of_list basis) i) g) basis) = 0)).
  Proof.
    intros basis Hmass Hw.
    unfold indexed_basis_covariance_positive_definite.
    split; intros Hproperty coefficients Hnonzero.
    - apply (proj1
        (indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot
          basis coefficients Hmass Hw)).
      apply Hproperty; exact Hnonzero.
    - apply (proj2
        (indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot
          basis coefficients Hmass Hw)).
      apply Hproperty; exact Hnonzero.
  Qed.

  (**
   [indexed_basis_covariance_positive_definite_iff_positive_composite_variances] (theorem) — Positive definiteness of the finite covariance basis is exactly strict positivity of the variance of every nonzero vector-weighted composite score.
   Mathematical meaning: Positive definiteness of the finite covariance basis is exactly strict positivity of the variance of every nonzero vector-weighted composite score.
   Exact checked proposition: If total_mass=1, indexed_basis_covariance_positive_definite basis iff every coefficients:Vector.t R(length basis) with Vector.to_list coefficients <> repeat 0 (length basis) satisfies 0 < variance (weighted_basis_sum (Vector.to_list coefficients) basis).
   Premises and side conditions: The index and coefficient dimensions are enforced by Stdlib.Vectors.Vector.t and the finite basis length. The variance equality needs mass one but does not require positive weights for this algebraic equivalence.
   Proof/definition method: Unfold typed positive definiteness and rewrite each coefficient direction via the already proved indexed_basis_covariance_quadratic_as_variance, in both directions. No matrix multiplication, normalization proof, or custom list fold is repeated.
   Library reuse: indexed_basis_covariance_positive_definite, indexed_basis_covariance_quadratic_as_variance, Stdlib.Vectors.Vector.to_list.
   Boundary: This is a characterization of positive-definite covariance structure under the stated finite algebra, not an assertion that the chosen basis is nondegenerate or a spectral calculation.
   *)
  Theorem indexed_basis_covariance_positive_definite_iff_positive_composite_variances :
    forall basis,
      total_mass = 1 ->
      (indexed_basis_covariance_positive_definite basis <->
       forall coefficients : Vector.t R (length basis),
         Vector.to_list coefficients <> repeat 0 (length basis) ->
         0 < variance (weighted_basis_sum
           (Vector.to_list coefficients) basis)).
  Proof.
    intros basis Hmass.
    unfold indexed_basis_covariance_positive_definite.
    split; intros Hproperty coefficients Hnonzero.
    - rewrite <- (indexed_basis_covariance_quadratic_as_variance
        basis coefficients Hmass).
      apply Hproperty; exact Hnonzero.
    - rewrite (indexed_basis_covariance_quadratic_as_variance
        basis coefficients Hmass).
      apply Hproperty; exact Hnonzero.
  Qed.

  (**
   [indexed_basis_covariance_positive_definite_iff_no_nonzero_basis_orthogonal_direction] (theorem) — A finite typed covariance basis is positive definite exactly when no nonzero coefficient vector yields a composite score orthogonal to all basis scores.
   Mathematical meaning: A finite typed covariance basis is positive definite exactly when no nonzero coefficient vector yields a composite score orthogonal to all basis scores.
   Exact checked proposition: Under unit-mass nonnegative sampled weights, indexed_basis_covariance_positive_definite basis iff forall nonzero typed coefficients, not (forall g in basis, covariance (weighted_basis_sum (Vector.to_list coefficients) basis) g = 0).
   Premises and side conditions: All quantification uses finite basis membership and length-checked real vectors. Repeated basis elements are allowed and independence is not assumed; lack of orthogonal directions is the exact condition.
   Proof/definition method: Apply the existing positive quadratic iff non-orthogonality to basis scores theorem pointwise to every nonzero coefficient vector, preserving the normalized nonnegative sample premises.
   Library reuse: indexed_basis_covariance_quadratic_positive_iff_not_uncorrelated_with_basis, indexed_basis_covariance_positive_definite and Stdlib.List.
   Boundary: This is an equivalent structural criterion, not a covariance eigenvalue computation, numerical rank algorithm or empirical correlation claim.
   *)
  Theorem indexed_basis_covariance_positive_definite_iff_no_nonzero_basis_orthogonal_direction :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_positive_definite basis <->
       forall coefficients : Vector.t R (length basis),
         Vector.to_list coefficients <> repeat 0 (length basis) ->
         ~ (forall g, In g basis ->
              covariance (weighted_basis_sum
                (Vector.to_list coefficients) basis) g = 0)).
  Proof.
    intros basis Hmass Hw.
    unfold indexed_basis_covariance_positive_definite.
    split; intros Hproperty coefficients Hnonzero.
    - apply (proj1
        (indexed_basis_covariance_quadratic_positive_iff_not_uncorrelated_with_basis
          basis coefficients Hmass Hw)).
      apply Hproperty; exact Hnonzero.
    - apply (proj2
        (indexed_basis_covariance_quadratic_positive_iff_not_uncorrelated_with_basis
          basis coefficients Hmass Hw)).
      apply Hproperty; exact Hnonzero.
  Qed.

  (**
   [indexed_basis_covariance_positive_definite_iff_no_nonzero_zero_quadratic] (theorem) — For normalized nonnegative finite sample weights, covariance positive definiteness is equivalent to the absence of nonzero coefficient directions with exactly zero quadratic form.
   Mathematical meaning: For normalized nonnegative finite sample weights, covariance positive definiteness is equivalent to the absence of nonzero coefficient directions with exactly zero quadratic form.
   Exact checked proposition: Under total_mass=1 and nonnegative sampled weights, indexed_basis_covariance_positive_definite basis iff every nonzero Vector.t coefficient vector has indexed_basis_covariance_quadratic_form basis coefficients <> 0.
   Premises and side conditions: The covariance quadratic must be positive semidefinite under the displayed mass and nonnegativity assumptions; without PSD, a nonzero negative quadratic would make the right side insufficient.
   Proof/definition method: In the positive-to-nonzero direction apply ordinary real linear arithmetic. Conversely combine nonzero quadratic with the already proved indexed quadratic nonnegativity and infer strict positivity using Stdlib.Lra.
   Library reuse: indexed_basis_covariance_quadratic_nonnegative, indexed_basis_covariance_positive_definite and Stdlib.Lra.
   Boundary: This is kernel triviality of an exact PSD finite covariance form, not construction of a kernel basis or rank-nullity theorem.
   *)
  Theorem indexed_basis_covariance_positive_definite_iff_no_nonzero_zero_quadratic :
    forall basis,
      total_mass = 1 ->
      (forall x, In x samples -> 0 <= weight x) ->
      (indexed_basis_covariance_positive_definite basis <->
       forall coefficients : Vector.t R (length basis),
         Vector.to_list coefficients <> repeat 0 (length basis) ->
         indexed_basis_covariance_quadratic_form basis coefficients <> 0).
  Proof.
    intros basis Hmass Hw.
    unfold indexed_basis_covariance_positive_definite.
    split; intros Hproperty coefficients Hnonzero.
    - pose proof (Hproperty coefficients Hnonzero) as Hpositive.
      lra.
    - pose proof (indexed_basis_covariance_quadratic_nonnegative
        basis coefficients Hmass Hw) as Hnonnegative.
      pose proof (Hproperty coefficients Hnonzero) as Hnotzero.
      lra.
  Qed.

  (**
   [indexed_basis_covariance_quadratic_positive_of_distinct_support_values] (theorem) — A pair of positively weighted sampled outcomes distinguished by a typed coefficient-composite score witnesses a strictly positive covariance quadratic.
   Mathematical meaning: A pair of positively weighted sampled outcomes distinguished by a typed coefficient-composite score witnesses a strictly positive covariance quadratic.
   Exact checked proposition: For any basis and coefficients:Vector.t R(length basis), normalized nonnegative weights and x,y in samples with strictly positive weights, unequal weighted_basis_sum coefficient_list basis scores at x and y imply 0 < indexed_basis_covariance_quadratic_form basis coefficients.
   Premises and side conditions: Both x and y must occur in the sampled list and carry positive weight. No independent basis scores, distinct input outcomes or Gaussian distribution is assumed; only their evaluated composite scores must differ.
   Proof/definition method: Invoke the existing indexed quadratic positivity iff no positive-support constant and refute constancy with the two witnessed sample values.
   Library reuse: indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support, Stdlib logical connectives and the maintained weighted_basis_sum.
   Boundary: This proves strict positivity for one specified coefficient direction only; it is not a numerical lower bound, coefficient injectivity or a matrix-rank calculation.
   *)
  Theorem indexed_basis_covariance_quadratic_positive_of_distinct_support_values :
    forall basis (coefficients : Vector.t R (length basis)) x y,
      total_mass = 1 ->
      (forall z, In z samples -> 0 <= weight z) ->
      In x samples -> 0 < weight x ->
      In y samples -> 0 < weight y ->
      weighted_basis_sum (Vector.to_list coefficients) basis x <>
        weighted_basis_sum (Vector.to_list coefficients) basis y ->
      0 < indexed_basis_covariance_quadratic_form basis coefficients.
  Proof.
    intros basis coefficients x y Hmass Hw Hx Hwx Hy Hwy Hdifferent.
    apply (proj2
      (indexed_basis_covariance_quadratic_positive_iff_nonconstant_on_support
        basis coefficients Hmass Hw)).
    intros [c Hconstant].
    apply Hdifferent.
    transitivity c.
    - apply Hconstant; assumption.
    - symmetry. apply Hconstant; assumption.
  Qed.

  (**
   [indexed_basis_covariance_positive_definite_of_separating_support_pairs] (theorem) — If every nonzero typed coefficient direction distinguishes some pair of positive-weight sample outcomes, then the entire finite covariance basis is positive definite.
   Mathematical meaning: If every nonzero typed coefficient direction distinguishes some pair of positive-weight sample outcomes, then the entire finite covariance basis is positive definite.
   Exact checked proposition: Under unit mass and nonnegative sampled weights, if forall coefficients:Vector.t R(length basis) with Vector.to_list coefficients <> repeat 0 (length basis), exists two positive-weight sampled outcomes whose weighted composite-score values differ, then indexed_basis_covariance_positive_definite basis.
   Premises and side conditions: Each nonzero coefficient vector must have its own possibly different witness pair; zero-weight samples do not count. This hypothesis does not require any externally defined finite-dimensional rank or eigenvalue theory.
   Proof/definition method: Unfold the typed positive-definiteness predicate, select the witness pair for each nonzero coefficient, and reuse the previously checked indexed pair-separation positivity theorem.
   Library reuse: indexed_basis_covariance_positive_definite, indexed_basis_covariance_quadratic_positive_of_distinct_support_values and Stdlib.Vectors.Vector.to_list.
   Boundary: A sufficient witness criterion for strict positive definiteness is established, not the necessity of pair witnesses or an algorithm to enumerate them.
   *)
  Theorem indexed_basis_covariance_positive_definite_of_separating_support_pairs :
    forall basis,
      total_mass = 1 ->
      (forall z, In z samples -> 0 <= weight z) ->
      (forall coefficients : Vector.t R (length basis),
        Vector.to_list coefficients <> repeat 0 (length basis) ->
        exists x y,
          In x samples /\ 0 < weight x /\
          In y samples /\ 0 < weight y /\
          weighted_basis_sum (Vector.to_list coefficients) basis x <>
            weighted_basis_sum (Vector.to_list coefficients) basis y) ->
      indexed_basis_covariance_positive_definite basis.
  Proof.
    intros basis Hmass Hw Hseparates.
    unfold indexed_basis_covariance_positive_definite.
    intros coefficients Hnonzero.
    destruct (Hseparates coefficients Hnonzero)
      as [x [y [Hx [Hwx [Hy [Hwy Hdifferent]]]]]].
    exact (indexed_basis_covariance_quadratic_positive_of_distinct_support_values
      basis coefficients x y Hmass Hw Hx Hwx Hy Hwy Hdifferent).
  Qed.

  (**
   [indexed_basis_covariance_quadratic_positive_of_nonzero_bounded_row_dot] (theorem) — A nonzero dot product against any dimension-safe covariance row is a direct witness of strictly positive covariance quadratic form.
   Mathematical meaning: A nonzero dot product against any dimension-safe covariance row is a direct witness of strictly positive covariance quadratic form.
   Exact checked proposition: For any typed coefficient vector and bounded Fin.t row index i, under unit mass and nonnegative sample weights, vector_dot coefficient_list (map (fun g => covariance (Vector.nth (Vector.of_list basis) i) g) basis) <> 0 implies 0 < indexed_basis_covariance_quadratic_form basis coefficients.
   Premises and side conditions: The bounded row and coefficient vector dimensions are enforced by standard Fin.t and Vector.t types. The covariance basis can be dependent and no positive-definiteness of the full matrix is assumed.
   Proof/definition method: Use the previously checked strict-positive-iff-not-all-bounded-row-dots theorem. A particular nonzero row refutes universal row nullity.
   Library reuse: indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot, Stdlib.Vectors.Fin and Vector, vector_dot.
   Boundary: This is an explicitly witnessed sufficient condition for one positive direction, not a statement that every row is nonzero or that the covariance matrix has full rank.
   *)
  Theorem indexed_basis_covariance_quadratic_positive_of_nonzero_bounded_row_dot :
    forall basis (coefficients : Vector.t R (length basis))
           (i : Fin.t (length basis)),
      total_mass = 1 ->
      (forall z, In z samples -> 0 <= weight z) ->
      vector_dot (Vector.to_list coefficients)
        (map (fun g => covariance
          (Vector.nth (Vector.of_list basis) i) g) basis) <> 0 ->
      0 < indexed_basis_covariance_quadratic_form basis coefficients.
  Proof.
    intros basis coefficients i Hmass Hw Hnonzero.
    apply (proj2
      (indexed_basis_covariance_quadratic_positive_iff_nonzero_bounded_row_dot
        basis coefficients Hmass Hw)).
    intro Hall.
    apply Hnonzero.
    apply Hall.
  Qed.

  (**
   [indexed_basis_covariance_not_positive_definite_of_nonzero_bounded_row_kernel] (theorem) — An explicitly nonzero coefficient vector annihilating every bounded covariance matrix row proves the finite covariance basis is not positive definite.
   Mathematical meaning: An explicitly nonzero coefficient vector annihilating every bounded covariance matrix row proves the finite covariance basis is not positive definite.
   Exact checked proposition: For normalized nonnegative finite sample weights, existence of coefficients:Vector.t R(length basis) whose list representation differs from repeat 0 and whose dot product against every Fin.t-indexed covariance row vanishes implies ~ indexed_basis_covariance_positive_definite basis.
   Premises and side conditions: The witness must be a genuine nonzero typed coefficient direction. The matrix need not be invertible; the theorem shows that the observed witness precludes positive definiteness.
   Proof/definition method: Specialize the existing positive-definite iff no-nonzero-bounded-row-kernel theorem to the assumed positive-definite basis and contradict its indexed-row kernel exclusion with the supplied coefficient witness.
   Library reuse: indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel, Stdlib.Vectors.Vector.to_list and Fin.t.
   Boundary: This refutes positive definiteness constructively from an explicit null vector; it does not compute the full nullspace, rank or algebraic multiplicity.
   *)
  Theorem indexed_basis_covariance_not_positive_definite_of_nonzero_bounded_row_kernel :
    forall basis (coefficients : Vector.t R (length basis)),
      total_mass = 1 ->
      (forall z, In z samples -> 0 <= weight z) ->
      Vector.to_list coefficients <> repeat 0 (length basis) ->
      (forall i : Fin.t (length basis),
        vector_dot (Vector.to_list coefficients)
          (map (fun g => covariance
            (Vector.nth (Vector.of_list basis) i) g) basis) = 0) ->
      ~ indexed_basis_covariance_positive_definite basis.
  Proof.
    intros basis coefficients Hmass Hw Hnonzero Hrows Hpositive.
    pose proof
      (proj1 (indexed_basis_covariance_positive_definite_iff_no_nonzero_bounded_row_kernel
        basis Hmass Hw) Hpositive) as Htrivial.
    apply (Htrivial coefficients Hnonzero).
    exact Hrows.
  Qed.

End FiniteProbabilityMoments.
