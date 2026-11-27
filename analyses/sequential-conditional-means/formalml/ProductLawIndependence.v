(** Module: ProductLawIndependence.v
    Purpose: Bridge joint-law factorization on an arbitrary source
    probability space to independence of the actual random variables.
    This is the converse of FormalML's product_pair_law; the forward
    direction reuses that theorem. In Gaussian applications the joint
    pushforward must still be proved to factorize, not assumed to do
    so merely because its covariance has zero off-diagonal blocks.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted source; kernel and assumption checks pending.
*)
From FormalML.ProbTheory Require Import
  ProductSpace RandomVariable Independence SigmaAlgebras ProbSpace.

Section JointProductLaw.
  Context {Omega X Y : Type}.
  Context {dom : SigmaAlgebra Omega}.
  Context (prob : ProbSpace dom).
  Context {sx : SigmaAlgebra X} {sy : SigmaAlgebra Y}.
  Context (x : Omega -> X) (y : Omega -> Y).
  Context {x_rv : RandomVariable dom sx x}.
  Context {y_rv : RandomVariable dom sy y}.

  (** The law of the pair is the product of its two marginal laws if
      the two variables are independent, and conversely. For the
      converse, evaluate equality of measures on each measurable
      rectangle and use the library's product rectangle formula.
      The assertion is for every measurable event, with no restriction
      to continuous densities or nonsingular distributions. *)
  Theorem independent_rvs_iff_product_joint_law :
    independent_rvs prob sx sy x y <->
    ps_equiv (product_ps (pullback_ps _ _ prob x)
                         (pullback_ps _ _ prob y))
             (pullback_ps _ _ prob (fun w => (x w, y w))).
  Proof.
    split.
    - apply product_pair_law.
    - intros Hlaw a b.
      unfold independent_events.
      pose proof (Hlaw (product_sa_event a b)) as Hrect.
      rewrite product_sa_product in Hrect.
      simpl in Hrect.
      rewrite <- Hrect.
      apply ps_proper.
      intro w; reflexivity.
  Qed.
End JointProductLaw.
