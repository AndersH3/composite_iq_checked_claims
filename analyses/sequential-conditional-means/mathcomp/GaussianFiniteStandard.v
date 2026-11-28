(** Module: GaussianFiniteStandard.v
    Purpose: Construct finite-dimensional standard Gaussian laws
    as recursively extended independent standard normal coordinates.
    Use the existing MathComp measurable tuple type, measurable cons,
    probability products and distribution of measurable maps. The
    empty history is the Dirac law on the unique empty tuple.
    Coordinate and rectangle laws are the first steps toward affine
    Gaussian laws and covariance-based residual independence.
    No multivariate Gaussian factorization is assumed.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted proof candidates; validation pending.
*)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals ereal topology normedtype.
From mathcomp Require Import numfun measure lebesgue_integral
  lebesgue_stieltjes_measure lebesgue_measure measurable_realfun.
From mathcomp.analysis Require Import normal_distribution random_variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section FiniteStandard.
Context {R : realType}.
Import MeasurableR.
Local Open Scope ereal_scope.
Local Notation G := (normal_prob (0%R : R) (1%R : R)).

(** Cons is the canonical tuple constructor, with the observation
    coordinate first and the remaining finite history second. *)
Definition gmc_history_cons (n : nat) (z : measurableTypeR R * (n.-tuple (measurableTypeR R))) : (n.+1.-tuple (measurableTypeR R)) :=
  [tuple of z.1 :: z.2].

(** The constructor is measurable by the library's measurable_cons
    theorem and the two measurable product projections. *)
Lemma gmc_history_cons_measurable n :
  measurable_fun [set: measurableTypeR R * (n.-tuple (measurableTypeR R))] (@gmc_history_cons n).
Proof.
rewrite /gmc_history_cons.
exact: measurable_cons measurable_fst measurable_snd.
Qed.

(* Register the constructor as a library measurable function so its
   distribution automatically inherits the probability structure. *)
HB.instance Definition _ n :=
  @isMeasurableFun.Build _ _ _ _ (@gmc_history_cons n)
    (@gmc_history_cons_measurable n).

(** The standard Gaussian history law in dimension n. At zero
    dimension use the Dirac probability on the empty tuple. At a
    successor dimension take the independent product of the scalar
    standard normal and the previous law, then transport by cons. *)
Fixpoint gmc_standard_history (n : nat) : probability ((n.-tuple (measurableTypeR R))) R :=
  match n as k return probability ((k.-tuple (measurableTypeR R))) R with
  | 0%N => [the probability ((0.-tuple (measurableTypeR R))) R of
      @dirac _ _ ([tuple] : (0.-tuple (measurableTypeR R))) R]
  | k.+1 => [the probability ((k.+1.-tuple (measurableTypeR R))) R of
      distribution
        [the probability (measurableTypeR R * (k.-tuple (measurableTypeR R)))%type R of
          G \x gmc_standard_history k]
        [mfun of @gmc_history_cons k]]
  end.

(** All dimensions, including the empty history, have total mass one
    by the registered probability-measure structure. *)
Theorem gmc_standard_history_normalized n :
  gmc_standard_history n [set: (n.-tuple (measurableTypeR R))] = 1.
Proof. exact: probability_setT. Qed.

(** The empty history agrees with the Dirac probability on its
    unique tuple, without requiring a nonzero dimension. *)
Theorem gmc_standard_history_empty (A : set ((0.-tuple (measurableTypeR R)))) :
  gmc_standard_history 0%N A = @dirac _ _ ([tuple] : (0.-tuple (measurableTypeR R))) R A.
Proof. reflexivity. Qed.

(** A head/tail cylinder pulls back along cons to the actual
    measurable product rectangle. The tail equality uses the
    tuple library's proof-irrelevant value injection. *)
Lemma gmc_history_cons_rectangle n (U : set R) (A : set ((n.-tuple (measurableTypeR R)))) :
  (@gmc_history_cons n) @^-1`
    [set t : (n.+1.-tuple (measurableTypeR R)) | U (tnth t ord0) /\ A [tuple of behead t]] =
  U `*` A.
Proof.
apply/seteqP; split.
- move=> [x t] H.
  change (U (tnth (@gmc_history_cons n (x,t)) ord0) /\
    A [tuple of behead (@gmc_history_cons n (x,t))]) in H.
  have Htail : [tuple of behead (@gmc_history_cons n (x,t))] = t.
  { apply/val_inj; reflexivity. }
  move: H.
  rewrite Htail /gmc_history_cons tnth0.
  by [].
- move=> [x t] H.
  change (U (tnth (@gmc_history_cons n (x,t)) ord0) /\
    A [tuple of behead (@gmc_history_cons n (x,t))]).
  have Htail : [tuple of behead (@gmc_history_cons n (x,t))] = t.
  { apply/val_inj; reflexivity. }
  by rewrite Htail /gmc_history_cons tnth0.
Qed.

(** The head and the entire tail have the asserted independent
    rectangle law, derived from the actual recursive construction.
    This is not merely an independence premise. *)
Theorem gmc_standard_history_rectangle n (U : set R) (A : set ((n.-tuple (measurableTypeR R)))) :
  measurable U -> measurable A ->
  gmc_standard_history n.+1
    [set t : (n.+1.-tuple (measurableTypeR R)) | U (tnth t ord0) /\ A [tuple of behead t]] =
  G U * gmc_standard_history n A.
Proof.
move=> mU mA.
change ((G \x gmc_standard_history n)
  ((@gmc_history_cons n) @^-1`
    [set t : (n.+1.-tuple (measurableTypeR R)) | U (tnth t ord0) /\ A [tuple of behead t]]) =
  G U * gmc_standard_history n A).
rewrite gmc_history_cons_rectangle.
exact: product_measure1E mU mA.
Qed.

(** The first coordinate has the scalar standard normal law:
    specialize the rectangle law to the whole tail space. *)
Theorem gmc_standard_history_head n (U : set R) :
  measurable U ->
  gmc_standard_history n.+1 [set t : (n.+1.-tuple (measurableTypeR R)) | U (tnth t ord0)] = G U.
Proof.
move=> mU.
have Hset : [set t : (n.+1.-tuple (measurableTypeR R)) | U (tnth t ord0)] =
  [set t : (n.+1.-tuple (measurableTypeR R)) | U (tnth t ord0) /\ [set: (n.-tuple (measurableTypeR R))] [tuple of behead t]].
{ apply/seteqP; split=> t H; [exact (conj H I)|exact (proj1 H)]. }
rewrite Hset.
transitivity (G U * gmc_standard_history n [set: (n.-tuple (measurableTypeR R))]).
- exact: gmc_standard_history_rectangle mU measurableT.
- transitivity (G U * 1).
  + exact (f_equal (fun v : \bar R => G U * v)
      (gmc_standard_history_normalized n)).
  + exact: mule1.
Qed.

(** The full remaining history has the previous-dimensional law,
    obtained by integrating out the first independent coordinate. *)
Theorem gmc_standard_history_tail n (A : set ((n.-tuple (measurableTypeR R)))) :
  measurable A ->
  gmc_standard_history n.+1 [set t : (n.+1.-tuple (measurableTypeR R)) | A [tuple of behead t]] =
  gmc_standard_history n A.
Proof.
move=> mA.
have Hset : [set t : (n.+1.-tuple (measurableTypeR R)) | A [tuple of behead t]] =
  [set t : (n.+1.-tuple (measurableTypeR R)) | [set: R] (tnth t ord0) /\ A [tuple of behead t]].
{ apply/seteqP; split=> t H; [exact (conj I H)|exact (proj2 H)]. }
rewrite Hset.
transitivity (G [set: R] * gmc_standard_history n A).
- exact: gmc_standard_history_rectangle measurableT mA.
- have Hg : G [set: R] = 1.
  { exact: probability_setT. }
  transitivity (1 * gmc_standard_history n A).
  + exact (f_equal (fun v : \bar R => v * gmc_standard_history n A) Hg).
  + exact: mul1e.
Qed.

(** Every coordinate of every nonempty finite history has the
    scalar standard Gaussian law. Induct on dimension using
    the library ordinal decomposition and tuple head/tail rules. *)
Theorem gmc_standard_history_coordinate n (i : 'I_n) (U : set R) :
  measurable U ->
  gmc_standard_history n [set t : (n.-tuple (measurableTypeR R)) | U (tnth t i)] = G U.
Proof.
elim: n => [|n IH] in i *.
- by case: i => j; rewrite ltn0.
- move=> mU.
  case: (unliftP ord0 i) => [j ->|->]; last exact: gmc_standard_history_head mU.
  pose A := [set t : (n.-tuple (measurableTypeR R)) | U (tnth t j)].
  have mA : measurable A.
  { have H := (@measurable_tnth _ (measurableTypeR R) n j)
      measurableT U mU.
    by rewrite setTI in H. }
  have Hset : [set t : (n.+1.-tuple (measurableTypeR R)) | U (tnth t (lift ord0 j))] =
    [set t : (n.+1.-tuple (measurableTypeR R)) | A [tuple of behead t]].
  { have Hj : inord j.+1 = lift ord0 j.
    { apply/val_inj; by rewrite inordK ?ltnS ?ltn_ord. }
    apply/seteqP; split=> t;
      by rewrite /A /= tnth_behead Hj. }
  rewrite Hset.
  transitivity (gmc_standard_history n A).
  + exact: gmc_standard_history_tail mA.
  + exact (IH j mU).
Qed.
End FiniteStandard.
