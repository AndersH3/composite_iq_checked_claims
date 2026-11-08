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
   [sum_finite] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: R) (xs : list Outcome) : R := FiniteSum.finite_sum f
   xs.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition sum_finite (f : Outcome -> R) (xs : list Outcome) : R :=
    FiniteSum.finite_sum f xs.

  (**
   [total_mass] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: R := sum_finite weight samples.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition total_mass : R := sum_finite weight samples.

  (**
   [expect] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: R) : R := sum_finite (fun x => weight x * f x) samples.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition expect (f : Outcome -> R) : R :=
    sum_finite (fun x => weight x * f x) samples.

  (**
   [covariance] (definition).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal construction: R) : R := expect (fun x => f x * g x) - expect f *
   expect g.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition covariance (f g : Outcome -> R) : R :=
    expect (fun x => f x * g x) - expect f * expect g.

  (**
   [variance] (definition).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal construction: R) : R := covariance f f.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition variance (f : Outcome -> R) : R := covariance f f.

  (**
   [centered_second_moment] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: R) : R := expect (fun x => (f x - expect f) * (f x -
   expect f)).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition centered_second_moment (f : Outcome -> R) : R :=
    expect (fun x => (f x - expect f) * (f x - expect f)).

  (**
   [sum_finite_ext] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: sum_finite f xs = sum_finite g xs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [sum_finite_add] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall xs f g, sum_finite (fun x => f x + g x) xs =
   sum_finite f xs + sum_finite g xs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_add..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [sum_finite_scale] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall xs a f, sum_finite (fun x => a * f x) xs = a *
   sum_finite f xs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_scale..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [sum_finite_nonnegative] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: 0 <= sum_finite f xs.
   Hypotheses: Requires enumerated-list membership where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_nonnegative.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [expectation_ext] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: expect f = expect g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably expect., sum_finite_ext..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem expectation_ext :
    forall f g, (forall x, f x = g x) -> expect f = expect g.
  Proof.
    intros f g Hfg.
    unfold expect.
    apply sum_finite_ext.
    intro x; rewrite Hfg; reflexivity.
  Qed.

  (**
   [expectation_add] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall f g, expect (fun x => f x + g x) = expect f +
   expect g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, ring/field
   normalization; notably expect., sum_finite_ext, sum_finite_add..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [expectation_scale] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall a f, expect (fun x => a * f x) = a * expect f.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, ring/field
   normalization; notably expect., sum_finite_ext, sum_finite_scale..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [expectation_zero] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: expect (fun _ => 0) = 0.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, ring/field
   normalization; notably expect., sum_finite_ext, FiniteSum.finite_sum_zero..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [expectation_constant] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall c, expect (fun _ => c) = c * total_mass.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization, definitional computation; notably sum_finite_ext,
   sum_finite_scale.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [expectation_constant_normalized] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: expect (fun _ => c) = c.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization; notably
   expectation_constant.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem expectation_constant_normalized :
    forall c, total_mass = 1 -> expect (fun _ => c) = c.
  Proof.
    intros c Hmass.
    rewrite expectation_constant, Hmass; ring.
  Qed.

  (**
   [expectation_sub] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall f g, expect (fun x => f x - g x) = expect f -
   expect g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas, ring/field
   normalization; notably FiniteSum.finite_sum_ext, FiniteSum.finite_sum_sub..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [expectation_affine] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: expect (fun x => a * f x + b) = a * expect f + b.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably expectation_add.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [expectation_nonnegative] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall f, (forall x, In x samples -> 0 <= weight x) ->
   (forall x, In x samples -> 0 <= f x) -> 0 <= expect f.
   Hypotheses: Requires nonnegative outcome weights; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, Stdlib Psatz nonlinear
   arithmetic; notably expect., sum_finite_nonnegative..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_symmetric] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f g, covariance f g = covariance g f.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably covariance., expectation_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_scale_first] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f g a, covariance (fun x => a * f x) g = a *
   covariance f g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably covariance., expectation_scale.,
   Rminus_eq_compat_r..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_add_first] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f g h, covariance (fun x => f x + g x) h =
   covariance f h + covariance g h.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably covariance., expectation_add.,
   expectation_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_scale_second] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f g a, covariance f (fun x => a * g x) = a *
   covariance f g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, definitional computation; notably
   covariance_symmetric., covariance_scale_first..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_add_second] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f g h, covariance f (fun x => g x + h x) =
   covariance f g + covariance f h.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, definitional computation; notably
   covariance_symmetric., covariance_add_first., covariance_symmetric.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_second_moment] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f, variance f = expect (fun x => f x * f x) -
   expect f * expect f.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem variance_second_moment :
    forall f,
      variance f = expect (fun x => f x * f x) -
                   expect f * expect f.
  Proof.
    intro f; reflexivity.
  Qed.

  (**
   [variance_of_scaled_score] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f a, variance (fun x => a * f x) = (a * a) *
   variance f.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   variance., covariance_scale_first.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_two_score_sum] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f g, variance (fun x => f x + g x) = variance f +
   variance g + 2 * covariance f g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   variance., covariance_add_first., covariance_add_second..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [centered_second_moment_identity] (theorem).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal conclusion: centered_second_moment f = variance f.
   Hypotheses: Requires mass normalized to one; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably centered_second_moment., expectation_ext,
   expectation_add.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_nonnegative] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f, total_mass = 1 -> (forall x, In x samples -> 0
   <= weight x) -> 0 <= variance f.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably centered_second_moment., expectation_nonnegative., Rle_0_sqr..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_with_constant_first] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (fun _ => c) f = 0.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization, definitional
   computation; notably covariance., expectation_constant_normalized,
   expectation_scale.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_shifted_score] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => f x + c) = variance f.
   Hypotheses: Requires mass normalized to one; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably variance., covariance_add_first.,
   covariance_add_second..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_extensional] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f g = covariance f' g'.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably covariance., expectation_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem covariance_extensional :
    forall f f' g g',
      (forall x, f x = f' x) ->
      (forall x, g x = g' x) ->
      covariance f g = covariance f' g'.
  Proof.
    intros f f' g g' Hf Hg.
    unfold covariance.
    rewrite (expectation_ext f f' Hf).
    rewrite (expectation_ext g g' Hg).
    assert (Hprod :
      expect (fun x => f x * g x) =
      expect (fun x => f' x * g' x)).
    { apply expectation_ext; intro x.
      rewrite Hf, Hg; reflexivity. }
    rewrite Hprod; reflexivity.
  Qed.

  (**
   [variance_extensional] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance f = variance g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably variance.,
   covariance_extensional.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem variance_extensional :
    forall f g, (forall x, f x = g x) ->
      variance f = variance g.
  Proof.
    intros f g Hfg.
    unfold variance.
    apply covariance_extensional; exact Hfg.
  Qed.

  (**
   [centered_score_has_zero_expectation] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: expect (fun x => f x - expect f) = 0.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization; notably
   expectation_sub.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_with_constant_second] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f (fun _ => c) = 0.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_symmetric., covariance_with_constant_first.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_invariant_under_first_shift] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (fun x => f x + c) g = covariance f g.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization; notably
   covariance_add_first., covariance_with_constant_first.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_invariant_under_second_shift] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f (fun x => g x + c) = covariance f g.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization; notably
   covariance_add_second., covariance_with_constant_second.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_two_weighted_scores] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f g a b, variance (fun x => a * f x + b * g x) =
   (a * a) * variance f + (b * b) * variance g + 2 * a * b * covariance f g.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   variance_of_two_score_sum., covariance_scale_first.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_of_two_weighted_pairs] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f g h k a b c d, covariance (fun x => a * f x + b
   * g x) (fun x => c * h x + d * k x) = a * c * covariance f h + a * d *
   covariance f k + b * c * covariance g h + b * d * covariance g k.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, ring/field normalization; notably
   covariance_add_first., covariance_add_second., covariance_add_second.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_two_score_average] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f g, variance (fun x => (f x + g x) / 2) =
   (variance f + variance g + 2 * covariance f g) / 4.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably variance_extensional,
   variance_of_scaled_score.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_two_unit_variance_average] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => (f x + g x) / 2) = (1 + covariance f
   g) / 2.
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization; notably
   variance_of_two_score_average..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_standardized_score] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => (f x - mu) / sd) = 1.
   Hypotheses: Requires mass normalized to one; explicit
   nonzero/strict-positive denominator or scale; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, ring/field normalization; notably
   variance_extensional, variance_of_scaled_score., variance_of_shifted_score.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_iq_reporting_scale] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => 100 + scale * ((f x - mu) / sd)) =
   scale * scale.
   Hypotheses: Requires mass normalized to one; explicit
   nonzero/strict-positive denominator or scale; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably variance_extensional,
   variance_of_shifted_score, variance_of_scaled_score..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [linear_combination] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: R))) (x : Outcome) : R := FiniteSum.finite_sum (fun c
   => fst c * snd c x) components.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas,
   ring/field normalization, definitional computation; notably
   linear_combination, FiniteSum.finite_sum_ext, FiniteSum.finite_sum_scale..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition linear_combination
    (components : list (R * (Outcome -> R))) (x : Outcome) : R :=
    FiniteSum.finite_sum (fun c => fst c * snd c x) components.

  (* Apply the built-in list fold to weighted component expectations. *)
  (**
   [linear_expectation] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: R))) : R := FiniteSum.finite_sum (fun c => fst c *
   expect (snd c)) components.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas,
   ring/field normalization, definitional computation; notably
   linear_combination, FiniteSum.finite_sum_ext, FiniteSum.finite_sum_scale..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition linear_expectation
    (components : list (R * (Outcome -> R))) : R :=
    FiniteSum.finite_sum (fun c => fst c * expect (snd c)) components.

  (* The covariance coefficient row is an ordinary list fold. *)
  (**
   [covariance_row] (definition).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal construction: R))) : R := FiniteSum.finite_sum (fun c => fst c *
   covariance f (snd c)) components.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas,
   ring/field normalization, definitional computation; notably
   linear_combination, FiniteSum.finite_sum_ext, FiniteSum.finite_sum_scale..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition covariance_row
    (f : Outcome -> R)
    (components : list (R * (Outcome -> R))) : R :=
    FiniteSum.finite_sum
      (fun c => fst c * covariance f (snd c)) components.

  (* The double covariance sum is a fold of coefficient-weighted
     covariance rows, reusing the row fold above. *)
  (**
   [covariance_quadratic_form] (definition).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal construction: R))) : R := FiniteSum.finite_sum (fun c => fst c *
   covariance_row (snd c) right) left.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas,
   ring/field normalization, definitional computation; notably
   linear_combination, FiniteSum.finite_sum_ext, FiniteSum.finite_sum_scale..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition covariance_quadratic_form
    (left right : list (R * (Outcome -> R))) : R :=
    FiniteSum.finite_sum
      (fun c => fst c * covariance_row (snd c) right) left.

  (**
   [expectation_of_general_weighted_sum] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall components, expect (linear_combination components)
   = linear_expectation components.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization, definitional computation; notably
   linear_combination, FiniteSum.finite_sum_ext, FiniteSum.finite_sum_scale..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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

  (**
   [covariance_of_general_weighted_second] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f (linear_combination components) =
   covariance_row f components.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, application of already-proved lemmas, definitional
   computation; notably covariance_with_constant_second, covariance_add_second,
   covariance_extensional.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Lemma covariance_of_general_weighted_second :
    forall f components,
      total_mass = 1 ->
      covariance f (linear_combination components) =
        covariance_row f components.
  Proof.
    intros f components Hmass.
    induction components as [|[b g] tail IH].
    - change (covariance f (fun _ => 0) = 0).
      apply covariance_with_constant_second; exact Hmass.
    - change
        (covariance f
          (fun x => b * g x + linear_combination tail x) =
         b * covariance f g + covariance_row f tail).
      rewrite covariance_add_second, covariance_scale_second.
      replace (covariance f
         (fun x => linear_combination tail x))
        with (covariance f (linear_combination tail)).
      + rewrite IH; reflexivity.
      + apply covariance_extensional; intro x; reflexivity.
  Qed.

  (**
   [covariance_of_general_weighted_sums] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (linear_combination left) (linear_combination
   right) = covariance_quadratic_form left right.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably covariance_symmetric,
   covariance_of_general_weighted_second, covariance_row.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem covariance_of_general_weighted_sums :
    forall left right,
      total_mass = 1 ->
      covariance (linear_combination left)
                 (linear_combination right) =
        covariance_quadratic_form left right.
  Proof.
    intros left right Hmass.
    rewrite (covariance_symmetric
      (linear_combination left) (linear_combination right)).
    rewrite (covariance_of_general_weighted_second
      (linear_combination right) left Hmass).
    unfold covariance_row, covariance_quadratic_form.
    apply FiniteSum.finite_sum_ext; intro c.
    rewrite (covariance_symmetric (linear_combination right) (snd c)).
    rewrite (covariance_of_general_weighted_second (snd c) right Hmass).
    reflexivity.
  Qed.

  (**
   [variance_of_general_weighted_sum] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (linear_combination components) =
   covariance_quadratic_form components components.
   Hypotheses: Requires mass normalized to one; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: application of already-proved lemmas; notably variance.,
   covariance_of_general_weighted_sums.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem variance_of_general_weighted_sum :
    forall components,
      total_mass = 1 ->
      variance (linear_combination components) =
        covariance_quadratic_form components components.
  Proof.
    intros components Hmass.
    unfold variance.
    apply covariance_of_general_weighted_sums; exact Hmass.
  Qed.

  (**
   [covariance_quadratic_form_nonnegative] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: 0 <= covariance_quadratic_form components components.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership where shown in the statement; all other
   constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably variance_nonnegative.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [mean_of_centered_standardized_score] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: expect (fun x => (f x - expect f) / sd) = 0.
   Hypotheses: Requires mass normalized to one; explicit
   nonzero/strict-positive denominator or scale where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably expectation_ext, expectation_scale.,
   centered_score_has_zero_expectation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [mean_of_iq_reporting_scale] (theorem).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: expect (fun x => 100 + scale * ((f x - expect f) / sd)) =
   100.
   Hypotheses: Requires mass normalized to one; explicit
   nonzero/strict-positive denominator or scale where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably expectation_ext, expectation_affine,
   mean_of_centered_standardized_score.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_invariant_under_both_shifts] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (fun x => f x + a) (fun x => g x + b) =
   covariance f g.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_invariant_under_first_shift,
   covariance_invariant_under_second_shift.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_of_centered_standardized_scores] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (fun x => (f x - expect f) / sd_f) (fun x =>
   (g x - expect g) / sd_g) = covariance f g / (sd_f * sd_g).
   Hypotheses: Requires mass normalized to one; explicit
   nonzero/strict-positive denominator or scale where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Psatz nonlinear arithmetic, ring/field normalization; notably
   covariance_extensional, covariance_scale_first,
   covariance_invariant_under_both_shifts.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [self_covariance_of_standardized_score] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (fun x => (f x - expect f) / sd) (fun x => (f
   x - expect f) / sd) = 1.
   Hypotheses: Requires mass normalized to one; explicit
   nonzero/strict-positive denominator or scale; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, Stdlib Psatz nonlinear arithmetic,
   ring/field normalization; notably
   covariance_of_centered_standardized_scores.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_three_score_average] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f g h, variance (fun x => (f x + g x + h x) / 3) =
   (variance f + variance g + variance h + 2 * covariance f g + 2 * covariance
   f h + 2 * covariance g h) / 9.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably variance_extensional,
   variance_of_scaled_score., variance_of_two_score_sum..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_three_standardized_score_average] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => (f x + g x + h x) / 3) = (1 + 2 * rho)
   / 3.
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic; notably
   variance_of_three_score_average.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_two_standardized_score_average] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => (f x + g x) / 2) = (1 + rho) / 2.
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, definitional computation; notably
   variance_of_two_unit_variance_average.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [sum_scores] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: R)) (x : Outcome) : R := FiniteSum.finite_sum (fun f =>
   f x) fs.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum, FiniteSum.finite_sum_add.,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition sum_scores (fs : list (Outcome -> R)) (x : Outcome) : R :=
    FiniteSum.finite_sum (fun f => f x) fs.

  (* Unweighted covariance matrix row: a standard list fold. *)
  (**
   [covariance_row_sum] (definition).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal construction: R)) : R := FiniteSum.finite_sum (covariance f) fs.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum, FiniteSum.finite_sum_add.,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition covariance_row_sum
      (f : Outcome -> R) (fs : list (Outcome -> R)) : R :=
    FiniteSum.finite_sum (covariance f) fs.

  (* Double covariance sum is a fold over the row-fold operator. *)
  (**
   [covariance_double_sum] (definition).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal construction: R)) : R := FiniteSum.finite_sum (fun f =>
   covariance_row_sum f gs) fs.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum, FiniteSum.finite_sum_add.,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition covariance_double_sum
      (fs gs : list (Outcome -> R)) : R :=
    FiniteSum.finite_sum (fun f => covariance_row_sum f gs) fs.

  (* Sum the covariance-matrix diagonal using Stdlib.List. *)
  (**
   [diagonal_variance_sum] (definition).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal construction: R)) : R := FiniteSum.finite_sum variance fs.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum, FiniteSum.finite_sum_add.,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition diagonal_variance_sum
      (fs : list (Outcome -> R)) : R :=
    FiniteSum.finite_sum variance fs.

  (**
   [unordered_covariance_sum] (fixpoint).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal construction: R)) : R := match fs with | [] => 0 | f :: tl =>
   covariance_row_sum f tl + unordered_covariance_sum tl end.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum, FiniteSum.finite_sum_add.,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Fixpoint unordered_covariance_sum
      (fs : list (Outcome -> R)) : R :=
    match fs with
    | [] => 0
    | f :: tl => covariance_row_sum f tl +
                 unordered_covariance_sum tl
    end.

  (**
   [covariance_double_sum_second_cons] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall fs f gs, covariance_double_sum fs (f :: gs) =
   covariance_row_sum f fs + covariance_double_sum fs gs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum, FiniteSum.finite_sum_add.,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_double_sum_symmetric] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall fs gs, covariance_double_sum fs gs =
   covariance_double_sum gs fs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum, FiniteSum.finite_sum_swap,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [double_sum_diagonal_off_diagonal] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall fs, covariance_double_sum fs fs =
   diagonal_variance_sum fs + 2 * unordered_covariance_sum fs.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization; notably
   covariance_double_sum_second_cons, variance.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [unweighted_scores_as_linear_combination] (lemma).
   Meaning: Relates explicit finite outcomes and weights to the corresponding
   marginal or joint quantity.
   Formal conclusion: forall fs x, sum_scores fs x = linear_combination (map
   (fun f => (1, f)) fs) x.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably sum_scores, FiniteSum.finite_sum_map.,
   FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [unweighted_covariance_row_as_weighted] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f fs, covariance_row_sum f fs = covariance_row f
   (map (fun g => (1, g)) fs).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably covariance_row_sum,
   FiniteSum.finite_sum_map., FiniteSum.finite_sum_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_with_sum_scores] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f (sum_scores fs) = covariance_row_sum f fs.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably covariance_extensional.,
   unweighted_scores_as_linear_combination.,
   covariance_of_general_weighted_second.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Lemma covariance_with_sum_scores :
    forall f fs, total_mass = 1 ->
      covariance f (sum_scores fs) = covariance_row_sum f fs.
  Proof.
    intros f fs Hmass.
    transitivity
      (covariance f
        (linear_combination (map (fun g => (1, g)) fs))).
    - apply covariance_extensional.
      + intro x; reflexivity.
      + intro x; apply unweighted_scores_as_linear_combination.
    - rewrite (covariance_of_general_weighted_second
        f (map (fun g => (1, g)) fs) Hmass).
      symmetry; apply unweighted_covariance_row_as_weighted.
  Qed.

  (**
   [covariance_of_sum_scores] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (sum_scores fs) (sum_scores gs) =
   covariance_double_sum fs gs.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_symmetric, covariance_with_sum_scores,
   covariance_row_sum.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Lemma covariance_of_sum_scores :
    forall fs gs, total_mass = 1 ->
      covariance (sum_scores fs) (sum_scores gs) =
        covariance_double_sum fs gs.
  Proof.
    intros fs gs Hmass.
    rewrite (covariance_symmetric (sum_scores fs) (sum_scores gs)).
    rewrite (covariance_with_sum_scores (sum_scores gs) fs Hmass).
    unfold covariance_row_sum, covariance_double_sum.
    apply FiniteSum.finite_sum_ext; intro f.
    rewrite (covariance_symmetric (sum_scores gs) f).
    apply covariance_with_sum_scores; exact Hmass.
  Qed.

  (**
   [variance_of_unweighted_sum] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (sum_scores fs) = covariance_double_sum fs fs.
   Hypotheses: Requires mass normalized to one; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: application of already-proved lemmas; notably variance.,
   covariance_of_sum_scores.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem variance_of_unweighted_sum :
    forall fs, total_mass = 1 ->
      variance (sum_scores fs) = covariance_double_sum fs fs.
  Proof.
    intros fs Hmass.
    unfold variance.
    apply covariance_of_sum_scores; exact Hmass.
  Qed.

  (**
   [variance_of_rescaled_unweighted_sum] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => sum_scores fs x / n) =
   (diagonal_variance_sum fs + 2 * unordered_covariance_sum fs) / (n * n).
   Hypotheses: Requires mass normalized to one; explicit
   nonzero/strict-positive denominator or scale; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, ring/field normalization; notably
   variance_extensional, variance_of_scaled_score., variance_of_unweighted_sum.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [diagonal_variance_sum_of_unit_scores] (lemma).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: diagonal_variance_sum fs = INR (length fs).
   Hypotheses: Requires list length or dimension constraints as stated;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably diagonal_variance_sum.,
   FiniteSum.finite_sum_ext_in., FiniteSum.finite_sum_const.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [equal_weight_variance_from_finite_covariances] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: variance (fun x => sum_scores fs x / n) = rho + (1 - rho)
   / n.
   Hypotheses: Requires mass normalized to one; list length or dimension
   constraints as stated; enumerated-list membership; unit-variance or stated
   moment hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic, Stdlib
   Psatz nonlinear arithmetic, ring/field normalization; notably
   variance_of_rescaled_unweighted_sum, diagonal_variance_sum_of_unit_scores,
   Hpairs..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [vector_dot] (definition).
   Meaning: Gives a precise computational or algebraic interpretation of the
   named construction or assertion.
   Formal construction: (xs ys : list R) : R := FiniteSum.finite_sum (fun p =>
   fst p * snd p) (combine xs ys).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition vector_dot (xs ys : list R) : R :=
    FiniteSum.finite_sum
      (fun p => fst p * snd p) (combine xs ys).

  (**
   [covariance_cross_matrix] (definition).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal construction: R))) : list (list R) := map (fun c => map (fun d =>
   covariance (snd c) (snd d)) right) left.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition covariance_cross_matrix
    (left right : list (R * (Outcome -> R))) : list (list R) :=
    map (fun c => map
      (fun d => covariance (snd c) (snd d)) right) left.

  (**
   [covariance_matrix] (definition).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal construction: R))) : list (list R) := covariance_cross_matrix
   components components.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition covariance_matrix
    (components : list (R * (Outcome -> R))) : list (list R) :=
    covariance_cross_matrix components components.

  (**
   [matrix_bilinear_form] (definition).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal construction: (left_coeffs right_coeffs : list R) (matrix : list
   (list R)) : R := vector_dot left_coeffs (map (vector_dot right_coeffs)
   matrix).
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition matrix_bilinear_form
    (left_coeffs right_coeffs : list R)
    (matrix : list (list R)) : R :=
    vector_dot left_coeffs (map (vector_dot right_coeffs) matrix).

  (**
   [matrix_quadratic_form] (definition).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal construction: (coeffs : list R) (matrix : list (list R)) : R :=
   matrix_bilinear_form coeffs coeffs matrix.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition matrix_quadratic_form
    (coeffs : list R) (matrix : list (list R)) : R :=
    matrix_bilinear_form coeffs coeffs matrix.

  (**
   [covariance_row_as_vector_dot] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: forall f components, vector_dot (map fst components) (map
   (fun c => covariance f (snd c)) components) = covariance_row f components.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Lemma covariance_row_as_vector_dot :
    forall f components,
      vector_dot (map fst components)
        (map (fun c => covariance f (snd c)) components) =
      covariance_row f components.
  Proof.
    intros f components.
    induction components as [|[a g] rest IH].
    - reflexivity.
    - change
        (a * covariance f g +
         vector_dot (map fst rest)
           (map (fun c => covariance f (snd c)) rest) =
         a * covariance f g + covariance_row f rest).
      rewrite IH; ring.
  Qed.

  (**
   [covariance_double_sum_as_matrix_product] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: forall left right, matrix_bilinear_form (map fst left)
   (map fst right) (covariance_cross_matrix left right) =
   covariance_quadratic_form left right.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, ring/field normalization, definitional computation;
   notably matrix_bilinear_form, covariance_row_as_vector_dot.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Lemma covariance_double_sum_as_matrix_product :
    forall left right,
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      covariance_quadratic_form left right.
  Proof.
    intros left right.
    unfold matrix_bilinear_form, covariance_cross_matrix.
    induction left as [|[a f] rest IH]; simpl.
    - reflexivity.
    - change
        (a * vector_dot (map fst right)
             (map (fun d => covariance f (snd d)) right) +
         vector_dot (map fst rest)
           (map (vector_dot (map fst right))
             (map (fun c =>
               map (fun d => covariance (snd c) (snd d)) right)
               rest)) =
         a * covariance_row f right +
           covariance_quadratic_form rest right).
      rewrite (covariance_row_as_vector_dot f right), IH.
      ring.
  Qed.

  (**
   [covariance_matrix_quadratic_form_identity] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: forall components, matrix_quadratic_form (map fst
   components) (covariance_matrix components) = covariance_quadratic_form
   components components.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   matrix_quadratic_form, covariance_double_sum_as_matrix_product..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_cross_matrix_bilinear_identity] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: matrix_bilinear_form (map fst left) (map fst right)
   (covariance_cross_matrix left right) = covariance (linear_combination left)
   (linear_combination right).
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_double_sum_as_matrix_product.,
   covariance_of_general_weighted_sums.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem covariance_cross_matrix_bilinear_identity :
    forall left right,
      total_mass = 1 ->
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      covariance (linear_combination left) (linear_combination right).
  Proof.
    intros left right Hmass.
    rewrite covariance_double_sum_as_matrix_product.
    symmetry.
    apply covariance_of_general_weighted_sums; exact Hmass.
  Qed.

  (* The coefficient-vector bilinear form of a cross-covariance
     matrix is symmetric under exchanging both score bases.
     The proof reuses the checked finite-basis representation and
     covariance symmetry instead of implementing a matrix transpose. *)
  (**
   [covariance_cross_matrix_bilinear_swap] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: matrix_bilinear_form (map fst left) (map fst right)
   (covariance_cross_matrix left right) = matrix_bilinear_form (map fst right)
   (map fst left) (covariance_cross_matrix right left).
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_cross_matrix_bilinear_identity, covariance_symmetric..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem covariance_cross_matrix_bilinear_swap :
    forall left right,
      total_mass = 1 ->
      matrix_bilinear_form (map fst left) (map fst right)
        (covariance_cross_matrix left right) =
      matrix_bilinear_form (map fst right) (map fst left)
        (covariance_cross_matrix right left).
  Proof.
    intros left right Hmass.
    rewrite (covariance_cross_matrix_bilinear_identity
      left right Hmass).
    rewrite (covariance_cross_matrix_bilinear_identity
      right left Hmass).
    apply covariance_symmetric.
  Qed.

  (**
   [covariance_matrix_quadratic_form_is_variance] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: matrix_quadratic_form (map fst components)
   (covariance_matrix components) = variance (linear_combination components).
   Hypotheses: Requires mass normalized to one; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_matrix_quadratic_form_identity.,
   variance_of_general_weighted_sum.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Theorem covariance_matrix_quadratic_form_is_variance :
    forall components,
      total_mass = 1 ->
      matrix_quadratic_form (map fst components)
        (covariance_matrix components) =
      variance (linear_combination components).
  Proof.
    intros components Hmass.
    rewrite covariance_matrix_quadratic_form_identity.
    symmetry.
    apply variance_of_general_weighted_sum; exact Hmass.
  Qed.

  (**
   [covariance_matrix_is_positive_semidefinite] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: 0 <= matrix_quadratic_form (map fst components)
   (covariance_matrix components).
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership where shown in the statement; all other
   constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_matrix_quadratic_form_is_variance, variance_nonnegative.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_at_most_half_sum_of_variances] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: 2 * covariance f g <= variance f + variance g.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, ring/field normalization; notably
   variance_nonnegative, variance_extensional, variance_of_two_weighted_scores.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_at_least_negative_half_sum_of_variances] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: - (variance f + variance g) <= 2 * covariance f g.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably variance_nonnegative,
   variance_of_two_score_sum.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_of_unit_variance_scores_bounded] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: -1 <= covariance f g /\ covariance f g <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably
   covariance_at_most_half_sum_of_variances,
   covariance_at_least_negative_half_sum_of_variances.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [average_of_two_unit_variance_scores_bounded] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: 0 <= variance (fun x => (f x + g x) / 2) /\ variance (fun
   x => (f x + g x) / 2) <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably
   covariance_of_unit_variance_scores_bounded,
   variance_of_two_unit_variance_average.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [feasible_average_pair_correlation_lower_bound] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: -1 / (n - 1) <= rho.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   list length or dimension constraints as stated; enumerated-list membership;
   unit-variance or stated moment hypotheses where shown in the statement; all
   other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, Stdlib Psatz nonlinear arithmetic, ring/field
   normalization; notably variance_nonnegative,
   equal_weight_variance_from_finite_covariances, Rinv_0_lt_compat.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_row_sum_bounded_by_count] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance_row_sum f fs <= INR (length fs).
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   list length or dimension constraints as stated; enumerated-list membership;
   unit-variance or stated moment hypotheses where shown in the statement; all
   other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably covariance_row_sum.,
   FiniteSum.finite_sum_monotone., covariance_of_unit_variance_scores_bounded.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [unordered_covariance_sum_bounded_by_pair_count] (lemma).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: 2 * unordered_covariance_sum fs <= INR (length fs) * (INR
   (length fs) - 1).
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   list length or dimension constraints as stated; enumerated-list membership;
   unit-variance or stated moment hypotheses where shown in the statement; all
   other constraints remain explicit.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, application of already-proved lemmas, Stdlib Lra
   linear arithmetic, Stdlib Psatz nonlinear arithmetic; notably
   covariance_row_sum_bounded_by_count.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [feasible_average_pair_correlation_upper_bound] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: forall fs n rho, total_mass = 1 -> (forall x, In x
   samples -> 0 <= weight x) -> n = INR (length fs) -> 1 < n -> (forall f, In f
   fs -> variance f = 1) -> 2 * unordered_covariance_sum fs = n * (n - 1) * rho
   -> rho <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   list length or dimension constraints as stated; enumerated-list membership;
   unit-variance or stated moment hypotheses where shown in the statement; all
   other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Psatz nonlinear arithmetic; notably
   unordered_covariance_sum_bounded_by_pair_count.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [feasible_average_pair_correlation_interval] (theorem).
   Meaning: Relates variance, square root, correlation or reliability
   parameters under the displayed numerical constraints.
   Formal conclusion: -1 / (n - 1) <= rho /\ rho <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   list length or dimension constraints as stated; enumerated-list membership;
   unit-variance or stated moment hypotheses where shown in the statement; all
   other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   feasible_average_pair_correlation_lower_bound,
   feasible_average_pair_correlation_upper_bound.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [nonnegative_quadratic_discriminant] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: forall A B C, 0 <= A -> 0 <= C -> (forall t, 0 <= A + 2 *
   t * B + t * t * C) -> B * B <= A * C.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, Stdlib Lra linear arithmetic, Stdlib Psatz nonlinear
   arithmetic, ring/field normalization; notably Rinv_0_lt_compat.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [finite_covariance_cauchy_schwarz_squared] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f g * covariance f g <= variance f * variance
   g.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   ring/field normalization; notably nonnegative_quadratic_discriminant.,
   variance_nonnegative, variance_of_two_score_sum.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [zero_variance_implies_zero_covariance_first] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f g = 0.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Psatz nonlinear arithmetic; notably
   finite_covariance_cauchy_schwarz_squared.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [zero_variance_implies_zero_covariance_second] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f g = 0.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   enumerated-list membership; unit-variance or stated moment hypotheses where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably covariance_symmetric., zero_variance_implies_zero_covariance_first.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [nonzero_covariance_implies_positive_variances] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: 0 < variance f /\ 0 < variance g.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   explicit nonzero/strict-positive denominator or scale; enumerated-list
   membership; unit-variance or stated moment hypotheses where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas, explicit case analysis,
   Stdlib Lra linear arithmetic; notably variance_nonnegative,
   zero_variance_implies_zero_covariance_first,
   zero_variance_implies_zero_covariance_second.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [weighted_basis_sum] (definition).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal construction: R)) (x : Outcome) : R := linear_combination (combine
   coefficients basis) x.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition weighted_basis_sum
    (coefficients : list R) (basis : list (Outcome -> R))
    (x : Outcome) : R :=
    linear_combination (combine coefficients basis) x.

  (**
   [basis_covariance_matrix] (definition).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal construction: R)) : list (list R) := map (fun f => map (fun g =>
   covariance f g) basis) basis.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition basis_covariance_matrix
    (basis : list (Outcome -> R)) : list (list R) :=
    map (fun f => map (fun g => covariance f g) basis) basis.

  (**
   [basis_cross_covariance_matrix] (definition).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal construction: R)) : list (list R) := map (fun f => map (fun g =>
   covariance f g) right) left.
   Hypotheses: A definition; its parameters and fields appear in the signature,
   with no silent statistical assumptions.
   Implementation: structural induction on a finite list or natural index,
   equational rewriting, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
   *)
  Definition basis_cross_covariance_matrix
    (left right : list (Outcome -> R)) : list (list R) :=
    map (fun f => map (fun g => covariance f g) right) left.

  (**
   [weighted_basis_sum_as_combination] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall coefficients basis x, weighted_basis_sum
   coefficients basis x = linear_combination (combine coefficients basis) x.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [split_as_projection_maps] (lemma).
   Meaning: Proves a structural list identity using Rocq's standard list
   operations.
   Formal conclusion: R))), split components = (map fst components, map snd
   components).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: structural induction on a finite list or natural index,
   equational rewriting, definitional computation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [coefficients_of_combine] (lemma).
   Meaning: Proves a structural list identity using Rocq's standard list
   operations.
   Formal conclusion: map fst (combine coefficients basis) = coefficients.
   Hypotheses: Requires list length or dimension constraints as stated where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably combine_split, split_as_projection_maps, f_equal.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [basis_of_combine] (lemma).
   Meaning: Proves a structural list identity using Rocq's standard list
   operations.
   Formal conclusion: map snd (combine coefficients basis) = basis.
   Hypotheses: Requires list length or dimension constraints as stated where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably combine_split, split_as_projection_maps, f_equal.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_matrix_uses_only_basis] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: forall components, covariance_matrix components =
   basis_covariance_matrix (map snd components).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably covariance_matrix, map_map., map_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_cross_matrix_uses_only_bases] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: forall left right, covariance_cross_matrix left right =
   basis_cross_covariance_matrix (map snd left) (map snd right).
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably covariance_cross_matrix, map_map.,
   map_ext.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [fixed_basis_covariance_matrix_representation] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: covariance_matrix (combine coefficients basis) =
   basis_covariance_matrix basis.
   Hypotheses: Requires list length or dimension constraints as stated where
   shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, definitional computation; notably
   covariance_matrix_uses_only_basis., basis_of_combine.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [fixed_basis_weighted_variance_identity] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (weighted_basis_sum coefficients basis) =
   matrix_quadratic_form coefficients (basis_covariance_matrix basis).
   Hypotheses: Requires mass normalized to one; list length or dimension
   constraints as stated; unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably variance_extensional, weighted_basis_sum_as_combination.,
   covariance_matrix_quadratic_form_is_variance.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [fixed_basis_covariance_matrix_positive_semidefinite] (theorem).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: 0 <= matrix_quadratic_form coefficients
   (basis_covariance_matrix basis).
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   list length or dimension constraints as stated; enumerated-list membership
   where shown in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably variance_nonnegative.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [normalized_covariance_is_between_minus_one_and_one] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: -1 <= covariance f g / (sd_f * sd_g) /\ covariance f g /
   (sd_f * sd_g) <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   explicit nonzero/strict-positive denominator or scale; enumerated-list
   membership; unit-variance or stated moment hypotheses where shown in the
   statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, Stdlib Lra linear arithmetic, Stdlib Psatz nonlinear
   arithmetic, ring/field normalization; notably
   finite_covariance_cauchy_schwarz_squared, Rinv_0_lt_compat.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [centered_standardized_covariance_in_unit_interval] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: -1 <= covariance (fun x => (f x - expect f) / sd_f) (fun
   x => (g x - expect g) / sd_g) /\ covariance (fun x => (f x - expect f) /
   sd_f) (fun x => (g x - expect g) / sd_g) <= 1.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   explicit nonzero/strict-positive denominator or scale; enumerated-list
   membership; unit-variance or stated moment hypotheses where shown in the
   statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic; notably
   covariance_of_centered_standardized_scores,
   normalized_covariance_is_between_minus_one_and_one.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [unit_covariance_one_iff_difference_has_zero_variance] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f g = 1 <-> variance (fun x => f x - g x) = 0.
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   Stdlib Lra linear arithmetic, ring/field normalization; notably
   variance_extensional, variance_of_two_weighted_scores, Hidentity..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [unit_covariance_minus_one_iff_sum_has_zero_variance] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance f g = -1 <-> variance (fun x => f x + g x) =
   0.
   Hypotheses: Requires unit-variance or stated moment hypotheses where shown
   in the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, Stdlib Lra linear arithmetic; notably
   variance_of_two_score_sum.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_affine_score] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => a * f x + b) = (a * a) * variance f.
   Hypotheses: Requires mass normalized to one; unit-variance or stated moment
   hypotheses where shown in the statement; all other constraints remain
   explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably variance_of_shifted_score, variance_of_scaled_score..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [covariance_of_affine_scores] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: covariance (fun x => a * f x + b) (fun x => c * g x + d)
   = a * c * covariance f g.
   Hypotheses: Requires mass normalized to one where shown in the statement;
   all other constraints remain explicit.
   Proof outline: equational rewriting, ring/field normalization; notably
   covariance_invariant_under_first_shift,
   covariance_invariant_under_second_shift, covariance_scale_first.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [basis_covariance_matrix_row_count] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: forall basis, length (basis_covariance_matrix basis) =
   length basis.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   basis_covariance_matrix., length_map..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [basis_covariance_matrix_column_count] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: length row = length basis.
   Hypotheses: Requires list length or dimension constraints as stated;
   enumerated-list membership where shown in the statement; all other
   constraints remain explicit.
   Proof outline: application of already-proved lemmas, explicit case analysis;
   notably basis_covariance_matrix, in_map_iff, length_map..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [basis_cross_covariance_matrix_row_count] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: forall left right, length (basis_cross_covariance_matrix
   left right) = length left.
   Hypotheses: Exactly the quantified hypotheses displayed in the statement;
   there are no hidden global probability or distribution axioms.
   Proof outline: application of already-proved lemmas; notably
   basis_cross_covariance_matrix., length_map..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [basis_cross_covariance_matrix_column_count] (lemma).
   Meaning: Relates finite covariance entries and coefficient-weighted matrix
   or quadratic-form expressions.
   Formal conclusion: length row = length right.
   Hypotheses: Requires list length or dimension constraints as stated;
   enumerated-list membership where shown in the statement; all other
   constraints remain explicit.
   Proof outline: application of already-proved lemmas, explicit case analysis;
   notably basis_cross_covariance_matrix, in_map_iff, length_map..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [sum_finite_zero_implies_zero_terms] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall xs h, (forall x, In x xs -> 0 <= h x) ->
   sum_finite h xs = 0 -> forall x, In x xs -> h x = 0.
   Hypotheses: Requires enumerated-list membership where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_nonnegative_zero.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [zero_variance_is_constant_on_positive_mass] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: forall f x, total_mass = 1 -> (forall y, In y samples ->
   0 <= weight y) -> variance f = 0 -> In x samples -> 0 < weight x -> f x =
   expect f.
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   explicit nonzero/strict-positive denominator or scale; enumerated-list
   membership; unit-variance or stated moment hypotheses where shown in the
   statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   explicit case analysis, Stdlib Lra linear arithmetic; notably
   centered_second_moment_identity, Rmult_le_pos., Rle_0_sqr..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [null_covariance_direction_constant_on_positive_mass] (theorem).
   Meaning: Establishes an exact covariance identity or bound for the specified
   finite score functions.
   Formal conclusion: weighted_basis_sum coefficients basis x = expect
   (weighted_basis_sum coefficients basis).
   Hypotheses: Requires mass normalized to one; nonnegative outcome weights;
   explicit nonzero/strict-positive denominator or scale; list length or
   dimension constraints as stated; enumerated-list membership where shown in
   the statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas;
   notably zero_variance_is_constant_on_positive_mass,
   fixed_basis_weighted_variance_identity, Hquadratic..
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [sum_scores_permutation_invariant] (lemma).
   Meaning: Establishes finite-sum or finite-expectation algebra while
   retaining the original sum semantics.
   Formal conclusion: forall x, sum_scores fs x = sum_scores gs x.
   Hypotheses: Requires Stdlib list-permutation premise where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   FiniteSum.finite_sum_permutation.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [variance_of_permuted_score_sum] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (sum_scores fs) = variance (sum_scores gs).
   Hypotheses: Requires Stdlib list-permutation premise where shown in the
   statement; all other constraints remain explicit.
   Proof outline: application of already-proved lemmas; notably
   variance_extensional, sum_scores_permutation_invariant.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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
   [equal_weight_variance_permutation_invariant] (theorem).
   Meaning: Establishes a finite-sample variance identity or bound, including
   all stated scaling assumptions.
   Formal conclusion: variance (fun x => sum_scores fs x / n) = variance (fun x
   => sum_scores gs x / n).
   Hypotheses: Requires Stdlib list-permutation premise where shown in the
   statement; all other constraints remain explicit.
   Proof outline: equational rewriting, application of already-proved lemmas,
   definitional computation; notably variance_extensional,
   sum_scores_permutation_invariant.
   Library discipline: Stdlib.List, Sorting.Permutation, Reals and FiniteSum's
   reusable fold, extensionality, monotonicity and Fubini lemmas.
   Scope: No assertion about Gaussian covariance, continuous random variables
   or observed IQ distributions follows from this finite model.
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

End FiniteProbabilityMoments.
