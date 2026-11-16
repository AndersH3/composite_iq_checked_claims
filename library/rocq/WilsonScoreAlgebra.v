(** Module: WilsonScoreAlgebra.v
 Purpose: Prove exact Wilson score interval inversion and root certificates
 used by the Hoeflin, Towers, and Sequential simulation reports.
 Mathematical representation: Real sample size n, observed fraction h,
 critical value z, and candidate probability p; the quadratic score
 polynomial is completed into a squared center displacement minus a radicand.
 Explicit hypotheses: n>0 is demanded for inversion and root arithmetic;
 0<=h<=1 is required for statistical frequency/radius bounds, and an
 explicitly certified nonnegative r supplies the square-root identity.
 Library use: Rocq Stdlib Reals, Ring, Lra, Psatz, and Field. No new
 binomial probability mass function, square-root implementation or normal CDF.
 Limitations: These are EXACT polynomial score inversions; nominal coverage
 of Wilson intervals is approximate and is NOT asserted or kernel proved.
 Reproduction: rocq compile WilsonScoreAlgebra.v with pinned Rocq 9.2.
 AI disclosure: OpenAI ChatGPT assisted with specifications, proof scripts,
 documentation and integration. The Rocq kernel decides acceptance.
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
Open Scope R_scope.

(** [wilson_total] (definition).
 Mathematical meaning: The strictly positive leading quadratic coefficient of the score inversion when n>0.
 Exact declaration: wilson_total (n z:R) : R := n+z*z.
 Premises and side conditions: This total real expression has no implicit
 probability distribution or Gaussian assumption. Interpreting a
 denominator as a statistical rate requires n>0 where indicated.
 Proof/definition method: Transparent ordinary real arithmetic; no new
 matrix, integration, sum, random-number, or probability implementation.
 Library reuse: Rocq Stdlib Reals, Ring, Lra, Psatz and Field.
 Boundary: Exact score polynomial algebra, not exact Wilson coverage,
 an empirically validated model, or a normal quantile theorem.
*)
Definition wilson_total (n z:R) : R := n+z*z.

(** [wilson_center] (definition).
 Mathematical meaning: The score quadratic's unnormalized center, where h is the observed success frequency.
 Exact declaration: wilson_center (n h z:R) : R := n*h+z*z/2.
 Premises and side conditions: This total real expression has no implicit
 probability distribution or Gaussian assumption. Interpreting a
 denominator as a statistical rate requires n>0 where indicated.
 Proof/definition method: Transparent ordinary real arithmetic; no new
 matrix, integration, sum, random-number, or probability implementation.
 Library reuse: Rocq Stdlib Reals, Ring, Lra, Psatz and Field.
 Boundary: Exact score polynomial algebra, not exact Wilson coverage,
 an empirically validated model, or a normal quantile theorem.
*)
Definition wilson_center (n h z:R) : R := n*h+z*z/2.

(** [wilson_radical_square] (definition).
 Mathematical meaning: The exactly factored, nonnegative squared Wilson radius.
 Exact declaration: wilson_radical_square (n h z:R) : R := z*z*(n*h*(1-h)+z*z/4).
 Premises and side conditions: This total real expression has no implicit
 probability distribution or Gaussian assumption. Interpreting a
 denominator as a statistical rate requires n>0 where indicated.
 Proof/definition method: Transparent ordinary real arithmetic; no new
 matrix, integration, sum, random-number, or probability implementation.
 Library reuse: Rocq Stdlib Reals, Ring, Lra, Psatz and Field.
 Boundary: Exact score polynomial algebra, not exact Wilson coverage,
 an empirically validated model, or a normal quantile theorem.
*)
Definition wilson_radical_square (n h z:R) : R := z*z*(n*h*(1-h)+z*z/4).

(** [wilson_score] (definition).
 Mathematical meaning: The score-inversion inequality polynomial; it is not a finite-sample coverage theorem.
 Exact declaration: wilson_score (n h z p:R) : R := n*(h-p)*(h-p)-z*z*p*(1-p).
 Premises and side conditions: This total real expression has no implicit
 probability distribution or Gaussian assumption. Interpreting a
 denominator as a statistical rate requires n>0 where indicated.
 Proof/definition method: Transparent ordinary real arithmetic; no new
 matrix, integration, sum, random-number, or probability implementation.
 Library reuse: Rocq Stdlib Reals, Ring, Lra, Psatz and Field.
 Boundary: Exact score polynomial algebra, not exact Wilson coverage,
 an empirically validated model, or a normal quantile theorem.
*)
Definition wilson_score (n h z p:R) : R := n*(h-p)*(h-p)-z*z*p*(1-p).

(** [wilson_lower] (definition).
 Mathematical meaning: The certified lower score root from a nonnegative radical r.
 Exact declaration: wilson_lower (n h z r:R) : R := (wilson_center n h z-r)/wilson_total n z.
 Premises and side conditions: This total real expression has no implicit
 probability distribution or Gaussian assumption. Interpreting a
 denominator as a statistical rate requires n>0 where indicated.
 Proof/definition method: Transparent ordinary real arithmetic; no new
 matrix, integration, sum, random-number, or probability implementation.
 Library reuse: Rocq Stdlib Reals, Ring, Lra, Psatz and Field.
 Boundary: Exact score polynomial algebra, not exact Wilson coverage,
 an empirically validated model, or a normal quantile theorem.
*)
Definition wilson_lower (n h z r:R) : R := (wilson_center n h z-r)/wilson_total n z.

(** [wilson_upper] (definition).
 Mathematical meaning: The certified upper score root from a nonnegative radical r.
 Exact declaration: wilson_upper (n h z r:R) : R := (wilson_center n h z+r)/wilson_total n z.
 Premises and side conditions: This total real expression has no implicit
 probability distribution or Gaussian assumption. Interpreting a
 denominator as a statistical rate requires n>0 where indicated.
 Proof/definition method: Transparent ordinary real arithmetic; no new
 matrix, integration, sum, random-number, or probability implementation.
 Library reuse: Rocq Stdlib Reals, Ring, Lra, Psatz and Field.
 Boundary: Exact score polynomial algebra, not exact Wilson coverage,
 an empirically validated model, or a normal quantile theorem.
*)
Definition wilson_upper (n h z r:R) : R := (wilson_center n h z+r)/wilson_total n z.

(** [wilson_total_positive] (theorem).
 Mathematical meaning: Positive sample size makes the quadratic score coefficient strictly positive, even at a zero quantile.
 Exact proposition: forall n z, 0<n -> 0<wilson_total n z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_total_positive : forall n z, 0<n -> 0<wilson_total n z.
Proof.
  intros n z Hn; unfold wilson_total; nra.
Qed.

(** [wilson_total_at_least_sample] (theorem).
 Mathematical meaning: The coefficient of the score quadratic is bounded below by the number of independent trials.
 Exact proposition: forall n z, n<=wilson_total n z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_total_at_least_sample : forall n z, n<=wilson_total n z.
Proof.
  intros n z; unfold wilson_total; nra.
Qed.

(** [wilson_total_zero_quantile] (theorem).
 Mathematical meaning: With no score penalty the quadratic coefficient is the ordinary sample size.
 Exact proposition: forall n, wilson_total n 0=n.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_total_zero_quantile : forall n, wilson_total n 0=n.
Proof.
  intro n; unfold wilson_total; field; nra.
Qed.

(** [wilson_center_nonnegative] (theorem).
 Mathematical meaning: For admissible empirical frequencies the score interval's unnormalized midpoint is nonnegative.
 Exact proposition: forall n h z, 0<=n -> 0<=h -> 0<=wilson_center n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_center_nonnegative : forall n h z, 0<=n -> 0<=h -> 0<=wilson_center n h z.
Proof.
  intros n h z Hn Hh; unfold wilson_center; nra.
Qed.

(** [wilson_center_le_total] (theorem).
 Mathematical meaning: For h at most one the midpoint numerator does not exceed the normalizing coefficient.
 Exact proposition: forall n h z, 0<=n -> h<=1 -> wilson_center n h z<=wilson_total n z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_center_le_total : forall n h z, 0<=n -> h<=1 -> wilson_center n h z<=wilson_total n z.
Proof.
  intros n h z Hn Hh; unfold wilson_center,wilson_total; nra.
Qed.

(** [wilson_center_complement] (theorem).
 Mathematical meaning: Complementing the empirical event maps the midpoint numerator into the complementary total.
 Exact proposition: forall n h z, wilson_center n (1-h) z = wilson_total n z - wilson_center n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_center_complement : forall n h z, wilson_center n (1-h) z = wilson_total n z - wilson_center n h z.
Proof.
  intros; unfold wilson_center,wilson_total; field; nra.
Qed.

(** [wilson_radical_complement] (theorem).
 Mathematical meaning: The score endpoint discriminant is invariant under changing success to failure.
 Exact proposition: forall n h z, wilson_radical_square n (1-h) z = wilson_radical_square n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_radical_complement : forall n h z, wilson_radical_square n (1-h) z = wilson_radical_square n h z.
Proof.
  intros; unfold wilson_radical_square; field; nra.
Qed.

(** [wilson_radical_nonnegative] (theorem).
 Mathematical meaning: The algebraic squared radius is nonnegative at every empirical Bernoulli frequency.
 Exact proposition: forall n h z, 0<=n -> 0<=h -> h<=1 -> 0<=wilson_radical_square n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_radical_nonnegative : forall n h z, 0<=n -> 0<=h -> h<=1 -> 0<=wilson_radical_square n h z.
Proof.
  intros n h z Hn Hh Hupper. unfold wilson_radical_square. assert (Ha:0<=h*(1-h)) by nra. assert (Hb:0<=n*(h*(1-h))) by (apply Rmult_le_pos; assumption). assert (Hc:0<=z*z) by nra. assert (Hd:0<=z*z/4) by nra. assert (He:0<=n*(h*(1-h))+z*z/4) by nra. apply Rmult_le_pos; [exact Hc|nra].
Qed.

(** [wilson_score_at_empirical] (theorem).
 Mathematical meaning: The score statistic at the observed empirical proportion has only its negative variance term.
 Exact proposition: forall n h z, wilson_score n h z h = - z*z*h*(1-h).
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_at_empirical : forall n h z, wilson_score n h z h = - z*z*h*(1-h).
Proof.
  intros; unfold wilson_score; field; nra.
Qed.

(** [wilson_score_empirical_nonpositive] (theorem).
 Mathematical meaning: The observed empirical frequency always satisfies the non-strict score inequality.
 Exact proposition: forall n h z, 0<=h -> h<=1 -> wilson_score n h z h <= 0.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_empirical_nonpositive : forall n h z, 0<=h -> h<=1 -> wilson_score n h z h <= 0.
Proof.
  intros n h z Hl Hu; rewrite wilson_score_at_empirical. assert (Hh:0<=h*(1-h)) by nra. assert (Hz:0<=z*z) by nra. nra.
Qed.

(** [wilson_score_empirical_strict] (theorem).
 Mathematical meaning: With nonzero z and a nondegenerate sample proportion the score inequality is strictly satisfied.
 Exact proposition: forall n h z, 0<h -> h<1 -> z<>0 -> wilson_score n h z h < 0.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_empirical_strict : forall n h z, 0<h -> h<1 -> z<>0 -> wilson_score n h z h < 0.
Proof.
  intros n h z Hl Hu Hz. rewrite wilson_score_at_empirical. assert (Hh:0<h*(1-h)) by nra. assert (Hz2:0<z*z) by nra. nra.
Qed.

(** [wilson_score_at_zero] (theorem).
 Mathematical meaning: At candidate probability zero the score inequality is the squared empirical count discrepancy.
 Exact proposition: forall n h z, wilson_score n h z 0 = n*h*h.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_at_zero : forall n h z, wilson_score n h z 0 = n*h*h.
Proof.
  intros; unfold wilson_score; field; nra.
Qed.

(** [wilson_score_at_one] (theorem).
 Mathematical meaning: At candidate probability one the score inequality is the squared observed failure-frequency discrepancy.
 Exact proposition: forall n h z, wilson_score n h z 1 = n*(1-h)*(1-h).
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_at_one : forall n h z, wilson_score n h z 1 = n*(1-h)*(1-h).
Proof.
  intros; unfold wilson_score; field; nra.
Qed.

(** [wilson_score_complement] (theorem).
 Mathematical meaning: The exact score inversion is invariant under exchanging success and failure.
 Exact proposition: forall n h z p, wilson_score n (1-h) z (1-p)=wilson_score n h z p.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_complement : forall n h z p, wilson_score n (1-h) z (1-p)=wilson_score n h z p.
Proof.
  intros; unfold wilson_score; field; nra.
Qed.

(** [wilson_score_quantile_sign] (theorem).
 Mathematical meaning: The score quadratic depends on the square of z and therefore is unchanged by replacing z with -z.
 Exact proposition: forall n h z p, wilson_score n h (-z) p=wilson_score n h z p.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_quantile_sign : forall n h z p, wilson_score n h (-z) p=wilson_score n h z p.
Proof.
  intros; unfold wilson_score; field; nra.
Qed.

(** [wilson_radical_quantile_sign] (theorem).
 Mathematical meaning: The squared Wilson radius is invariant under reversal of the quantile sign.
 Exact proposition: forall n h z, wilson_radical_square n h (-z)=wilson_radical_square n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_radical_quantile_sign : forall n h z, wilson_radical_square n h (-z)=wilson_radical_square n h z.
Proof.
  intros; unfold wilson_radical_square; field; nra.
Qed.

(** [wilson_center_quantile_sign] (theorem).
 Mathematical meaning: The Wilson midpoint does not depend on the sign of the normal critical value.
 Exact proposition: forall n h z, wilson_center n h (-z)=wilson_center n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_center_quantile_sign : forall n h z, wilson_center n h (-z)=wilson_center n h z.
Proof.
  intros; unfold wilson_center; field; nra.
Qed.

(** [wilson_total_quantile_sign] (theorem).
 Mathematical meaning: The Wilson normalization depends on the squared critical value, not its sign.
 Exact proposition: forall n z, wilson_total n (-z)=wilson_total n z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_total_quantile_sign : forall n z, wilson_total n (-z)=wilson_total n z.
Proof.
  intros; unfold wilson_total; field; nra.
Qed.

(** [wilson_score_zero_quantile] (theorem).
 Mathematical meaning: At z=0 the score inequality reduces to the sample-weighted squared discrepancy.
 Exact proposition: forall n h p, wilson_score n h 0 p = n*(h-p)*(h-p).
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_zero_quantile : forall n h p, wilson_score n h 0 p = n*(h-p)*(h-p).
Proof.
  intros; unfold wilson_score; field; nra.
Qed.

(** [wilson_score_zero_quantile_unique] (theorem).
 Mathematical meaning: For positive sample size the zero-quantile score vanishes exactly at the observed frequency.
 Exact proposition: forall n h p, 0<n -> wilson_score n h 0 p = 0 -> p=h.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_zero_quantile_unique : forall n h p, 0<n -> wilson_score n h 0 p = 0 -> p=h.
Proof.
  intros n h p Hn Hzero. rewrite wilson_score_zero_quantile in Hzero. apply Rmult_integral in Hzero. destruct Hzero as [Hfirst|Hdiff]. - apply Rmult_integral in Hfirst. destruct Hfirst as [Hnzero|Hdiff]; lra. - lra.
Qed.

(** [wilson_complete_square] (theorem).
 Mathematical meaning: The Wilson quadratic score is precisely a completed square scaled by its positive leading coefficient.
 Exact proposition: forall n h z p, wilson_total n z * wilson_score n h z p = (wilson_total n z*p - wilson_center n h z)*(wilson_total n z*p - wilson_center n h z) - wilson_radical_square n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_complete_square : forall n h z p, wilson_total n z * wilson_score n h z p = (wilson_total n z*p - wilson_center n h z)*(wilson_total n z*p - wilson_center n h z) - wilson_radical_square n h z.
Proof.
  intros; unfold wilson_total,wilson_score,wilson_center,wilson_radical_square; field; nra.
Qed.

(** [wilson_left_endpoint_discriminant] (theorem).
 Mathematical meaning: The squared midpoint minus the squared radius is a nonnegative multiple of the squared observed success proportion.
 Exact proposition: forall n h z, wilson_center n h z*wilson_center n h z-wilson_radical_square n h z = n*wilson_total n z*h*h.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_left_endpoint_discriminant : forall n h z, wilson_center n h z*wilson_center n h z-wilson_radical_square n h z = n*wilson_total n z*h*h.
Proof.
  intros; unfold wilson_center,wilson_radical_square,wilson_total; field; nra.
Qed.

(** [wilson_right_endpoint_discriminant] (theorem).
 Mathematical meaning: The complementary squared midpoint gap is the corresponding failure-frequency square.
 Exact proposition: forall n h z, (wilson_total n z-wilson_center n h z)*(wilson_total n z-wilson_center n h z)-wilson_radical_square n h z = n*wilson_total n z*(1-h)*(1-h).
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_right_endpoint_discriminant : forall n h z, (wilson_total n z-wilson_center n h z)*(wilson_total n z-wilson_center n h z)-wilson_radical_square n h z = n*wilson_total n z*(1-h)*(1-h).
Proof.
  intros; unfold wilson_center,wilson_radical_square,wilson_total; field; nra.
Qed.

(** [wilson_radical_zero_quantile] (theorem).
 Mathematical meaning: Zero score critical value gives zero uncertainty radius.
 Exact proposition: forall n h, wilson_radical_square n h 0=0.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_radical_zero_quantile : forall n h, wilson_radical_square n h 0=0.
Proof.
  intros; unfold wilson_radical_square; field; nra.
Qed.

(** [wilson_radical_zero_successes] (theorem).
 Mathematical meaning: The zero-success case has an exact positive fourth-order critical-value square as its radicand.
 Exact proposition: forall n z, wilson_radical_square n 0 z=z*z*z*z/4.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_radical_zero_successes : forall n z, wilson_radical_square n 0 z=z*z*z*z/4.
Proof.
  intros; unfold wilson_radical_square; field; nra.
Qed.

(** [wilson_radical_all_successes] (theorem).
 Mathematical meaning: The all-success case has the same radicand as the zero-success case.
 Exact proposition: forall n z, wilson_radical_square n 1 z=z*z*z*z/4.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_radical_all_successes : forall n z, wilson_radical_square n 1 z=z*z*z*z/4.
Proof.
  intros; unfold wilson_radical_square; field; nra.
Qed.

(** [wilson_score_inversion_scaled] (theorem).
 Mathematical meaning: Certified square-root radius converts the Wilson score inequality to an exact two-sided linear bound on the candidate probability.
 Exact proposition: forall n h z p r, 0<n -> 0<=r -> r*r=wilson_radical_square n h z -> (wilson_score n h z p<=0 <-> -r <= wilson_total n z*p - wilson_center n h z <= r).
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_inversion_scaled : forall n h z p r, 0<n -> 0<=r -> r*r=wilson_radical_square n h z -> (wilson_score n h z p<=0 <-> -r <= wilson_total n z*p - wilson_center n h z <= r).
Proof.
  intros n h z p r Hn Hr Hsquare. pose proof (wilson_total_positive n z Hn) as Hd. pose proof (wilson_complete_square n h z p) as Hid. rewrite <- Hsquare in Hid. split; intros H. - split; nra. - destruct H as [Hlo Hhi]; nra.
Qed.

(** [wilson_empirical_within_scaled_interval] (theorem).
 Mathematical meaning: Any certified Wilson radical includes the empirical proportion among the accepted score values.
 Exact proposition: forall n h z r, 0<n -> 0<=h -> h<=1 -> 0<=r -> r*r=wilson_radical_square n h z -> -r <= wilson_total n z*h-wilson_center n h z <=r.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_empirical_within_scaled_interval : forall n h z r, 0<n -> 0<=h -> h<=1 -> 0<=r -> r*r=wilson_radical_square n h z -> -r <= wilson_total n z*h-wilson_center n h z <=r.
Proof.
  intros n h z r Hn Hh Hu Hr Hsq. apply (proj1 (wilson_score_inversion_scaled n h z h r Hn Hr Hsq)); apply wilson_score_empirical_nonpositive; assumption.
Qed.

(** [wilson_left_radius_below_center] (theorem).
 Mathematical meaning: The Wilson radical cannot exceed the midpoint numerator for a valid sample proportion.
 Exact proposition: forall n h z r, 0<n -> 0<=h -> h<=1 -> 0<=r -> r*r=wilson_radical_square n h z -> r<=wilson_center n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_left_radius_below_center : forall n h z r, 0<n -> 0<=h -> h<=1 -> 0<=r -> r*r=wilson_radical_square n h z -> r<=wilson_center n h z.
Proof.
  intros n h z r Hn Hh Hu Hr Hsq. pose proof (wilson_center_nonnegative n h z (Rlt_le _ _ Hn) Hh) as Hc. pose proof (wilson_left_endpoint_discriminant n h z) as Hid. pose proof (wilson_total_positive n z Hn) as Hd. rewrite <- Hsq in Hid. assert (Hx:0<=n*wilson_total n z*h*h) by nra. destruct (Rle_dec r (wilson_center n h z)) as [Hordered|Hcontradiction]; [exact Hordered|]. apply Rnot_le_lt in Hcontradiction. exfalso; nra.
Qed.

(** [wilson_right_radius_below_complement] (theorem).
 Mathematical meaning: The Wilson radical cannot exceed the remaining mass from midpoint to one.
 Exact proposition: forall n h z r, 0<n -> 0<=h -> h<=1 -> 0<=r -> r*r=wilson_radical_square n h z -> r<=wilson_total n z-wilson_center n h z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_right_radius_below_complement : forall n h z r, 0<n -> 0<=h -> h<=1 -> 0<=r -> r*r=wilson_radical_square n h z -> r<=wilson_total n z-wilson_center n h z.
Proof.
  intros n h z r Hn Hh Hu Hr Hsq. pose proof (wilson_center_le_total n h z (Rlt_le _ _ Hn) Hu) as Hc. pose proof (wilson_right_endpoint_discriminant n h z) as Hid. pose proof (wilson_total_positive n z Hn) as Hd. rewrite <- Hsq in Hid. assert (Hx:0<=n*wilson_total n z*(1-h)*(1-h)) by nra. destruct (Rle_dec r (wilson_total n z-wilson_center n h z)) as [Hordered|Hcontradiction]; [exact Hordered|]. apply Rnot_le_lt in Hcontradiction. exfalso; nra.
Qed.

(** [wilson_endpoint_width] (theorem).
 Mathematical meaning: The algebraic Wilson interval has width twice its certified radius divided by the positive quadratic coefficient.
 Exact proposition: forall n h z r, 0<n -> wilson_upper n h z r-wilson_lower n h z r = 2*r/wilson_total n z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_endpoint_width : forall n h z r, 0<n -> wilson_upper n h z r-wilson_lower n h z r = 2*r/wilson_total n z.
Proof.
  intros n h z r Hn. unfold wilson_upper,wilson_lower. assert (Hd: wilson_total n z<>0) by (pose proof (wilson_total_positive n z Hn); lra). field; exact Hd.
Qed.

(** [wilson_endpoint_midpoint] (theorem).
 Mathematical meaning: The arithmetic midpoint of the two roots is the normalized Wilson center.
 Exact proposition: forall n h z r, 0<n -> (wilson_lower n h z r+wilson_upper n h z r)/2 = wilson_center n h z/wilson_total n z.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_endpoint_midpoint : forall n h z r, 0<n -> (wilson_lower n h z r+wilson_upper n h z r)/2 = wilson_center n h z/wilson_total n z.
Proof.
  intros n h z r Hn. unfold wilson_upper,wilson_lower. assert (Hd: wilson_total n z<>0) by (pose proof (wilson_total_positive n z Hn); lra). field; exact Hd.
Qed.

(** [wilson_lower_root] (theorem).
 Mathematical meaning: A certified radicand gives an exact lower root of the Wilson score equation.
 Exact proposition: forall n h z r, 0<n -> r*r=wilson_radical_square n h z -> wilson_score n h z (wilson_lower n h z r)=0.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_lower_root : forall n h z r, 0<n -> r*r=wilson_radical_square n h z -> wilson_score n h z (wilson_lower n h z r)=0.
Proof.
  intros n h z r Hn Hr. pose proof (wilson_complete_square n h z (wilson_lower n h z r)) as Hid. assert (Hd: wilson_total n z<>0) by (pose proof (wilson_total_positive n z Hn); lra). assert (He: wilson_total n z*wilson_lower n h z r-wilson_center n h z=-r) by (unfold wilson_lower; field; exact Hd). rewrite He in Hid; rewrite <- Hr in Hid. pose proof (wilson_total_positive n z Hn); nra.
Qed.

(** [wilson_upper_root] (theorem).
 Mathematical meaning: A certified radicand gives an exact upper root of the Wilson score equation.
 Exact proposition: forall n h z r, 0<n -> r*r=wilson_radical_square n h z -> wilson_score n h z (wilson_upper n h z r)=0.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_upper_root : forall n h z r, 0<n -> r*r=wilson_radical_square n h z -> wilson_score n h z (wilson_upper n h z r)=0.
Proof.
  intros n h z r Hn Hr. pose proof (wilson_complete_square n h z (wilson_upper n h z r)) as Hid. assert (Hd: wilson_total n z<>0) by (pose proof (wilson_total_positive n z Hn); lra). assert (He: wilson_total n z*wilson_upper n h z r-wilson_center n h z=r) by (unfold wilson_upper; field; exact Hd). rewrite He in Hid; rewrite <- Hr in Hid. pose proof (wilson_total_positive n z Hn); nra.
Qed.

(** [wilson_score_at_no_successes] (theorem).
 Mathematical meaning: At a zero observed proportion, the candidate zero probability exactly saturates the score inequality.
 Exact proposition: forall n z, wilson_score n 0 z 0=0.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_at_no_successes : forall n z, wilson_score n 0 z 0=0.
Proof.
  intros; rewrite wilson_score_at_zero; field; nra.
Qed.

(** [wilson_score_at_all_successes] (theorem).
 Mathematical meaning: At an observed proportion of one, candidate probability one exactly saturates the score inequality.
 Exact proposition: forall n z, wilson_score n 1 z 1=0.
 Premises and side conditions: All sample-size, observed-frequency,
 certified-radius, positivity, and endpoint assumptions needed for this
 mathematical conclusion are explicit in the Rocq statement. No hidden
 independence or Gaussian law is inferred from real algebra.
 Proof/definition method: Algebraic normalization, completed-square
 identity, and the maintained Rocq Stdlib Ring, Lra, Field or Psatz solvers;
 existing earlier results in this module are reused when relevant.
 Library reuse: Rocq Stdlib real numbers and canonical algebra tactics.
 Boundary: This is exact Wilson score inversion under supplied parameters,
 not a proof of an exact 95-percent coverage probability, nor an external
 statement about actual testing outcomes or numerical normal-tail accuracy.
*)
Theorem wilson_score_at_all_successes : forall n z, wilson_score n 1 z 1=0.
Proof.
  intros; rewrite wilson_score_at_one; field; nra.
Qed.

