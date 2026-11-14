(** Module: ReportRounding.v
   Purpose: Formalize the strict rational and square-root decimal-rounding
   certificates used by the sequential conditional-means IQ report.
   Mathematical model: Decimal reports are unique integer lattice indices
   in an open half-unit interval for the scaled real quantity. Integer
   certificate formulas match exact rational variance and mean fractions.
   Hypotheses: Rational denominator Q>0, positive scale T, nonnegative
   variance and nonnegative square-root grid indices where applicable.
   Boundaries: Arithmetic only. No Gaussian conditional-law construction,
   empirical population inference, or floating-point approximation is
   claimed. The nine instances are exact integer checks for the published
   values, not independent model-validation of the inputs.
   Library reuse: Stdlib.Reals, Lra, Psatz, ZArith, and the built-in
   integer normalization/decision procedures; no new summation engine.
   Verification: rocq compile ReportRounding.v under Rocq 9.2, after the
   maintained report modules. The theorem inventory links each result to
   the exact report appendix.
*)

From Stdlib Require Import Reals Lra Psatz ZArith Lia.
Open Scope R_scope.

(**
 [report_strict_rounding_interval] (definition) — Open nearest-grid cell.
 Mathematical meaning: The positive scale T sends a real quantity x
 into the unique open integer-centered half-unit cell indexed by t.
 Exact statement: 2*IZR t-1 < 2*T*x < 2*IZR t+1.
 Premises: None at definition level; sound certificate theorems assume T>0.
 Method: Transparent real inequalities, with no rounding algorithm.
 Library reuse: Stdlib.Reals.IZR and ordered-field operations.
 Boundary: Strict intervals exclude all halfway ties.
*)
Definition report_strict_rounding_interval
    (T : R) (t : Z) (x : R) : Prop :=
  2 * IZR t - 1 < 2 * T * x /\
  2 * T * x < 2 * IZR t + 1.

(**
 [report_strict_rounding_interval_unique] (theorem) — Exact uniqueness
 of a strictly nearest integer grid index.
 Mathematical meaning: Open half-unit cells associated with distinct
 integers do not overlap.
 Exact proposition: cell(T,t,x) and cell(T,j,x) imply t=j.
 Premises: Arbitrary real T and x; the inequalities themselves suffice.
 Method: Integer trichotomy and integer-to-real order compatibility,
 reducing overlapping interval constraints by Stdlib.Lra.
 Library reuse: Stdlib.ZArith.Z_lt_ge_dec, Z.eq_dec, IZR_le,
 plus_IZR, Stdlib.Lia and Lra.
 Boundary: The statement proves uniqueness; existence needs a separate
 certificate and halfway ties are deliberately excluded.
*)
Theorem report_strict_rounding_interval_unique :
  forall T x (t j : Z),
    report_strict_rounding_interval T t x ->
    report_strict_rounding_interval T j x ->
    t = j.
Proof.
  intros T x t j [Htl Htu] [Hjl Hju].
  destruct (Z_lt_ge_dec t j) as [Hlt | Hge].
  - assert (Hgap : (t + 1 <= j)%Z) by lia.
    apply IZR_le in Hgap.
    rewrite plus_IZR in Hgap.
    simpl in Hgap.
    lra.
  - destruct (Z.eq_dec t j) as [Heq | Hneq].
    + exact Heq.
    + assert (Hgap : (j + 1 <= t)%Z) by lia.
      apply IZR_le in Hgap.
      rewrite plus_IZR in Hgap.
      simpl in Hgap.
      lra.
Qed.

(**
 [report_rational_certificate_sound] (theorem) — Rational two-decimal
 rounding from the strict gap certificate in the report.
 Mathematical meaning: The integer test Q>2|T*P-t*Q| puts the exact
 rational P/Q in the unique nearest grid cell t/T.
 Exact proposition: T>0, Q>0 and Q-2*|TP-tQ|>0 imply
 cell(T,t,P/Q).
 Premises: Positive scale and denominator; P may be any signed real.
 Method: Split the standard real absolute-value definition by sign;
 cancel the nonzero real denominator and use ordered-field arithmetic.
 Library reuse: Stdlib.Reals.Rcase_abs/Rabs, Stdlib.Field, Psatz.nra.
 Boundary: Strict gap excludes ties. It proves exact arithmetic, not
 any population model or approximate floating-point computation.
*)
Theorem report_rational_certificate_sound :
  forall P Q T (t : Z),
    0 < T ->
    0 < Q ->
    0 < Q - 2 * Rabs (T * P - IZR t * Q) ->
    report_strict_rounding_interval T t (P / Q).
Proof.
  intros P Q T t HT HQ Hcertificate.
  assert (Hquot : Q * (P / Q) = P).
  { field; lra. }
  unfold report_strict_rounding_interval.
  unfold Rabs in Hcertificate.
  destruct (Rcase_abs (T * P - IZR t * Q)) as [Hnegative | Hnonnegative];
    split; nra.
Qed.

(**
 [report_sqrt_variance_certificate_sound] (theorem) — Exact strict
 rounded standard deviation from the two squared-interval tests.
 Mathematical meaning: Positive lower and upper square differences
 imply that sqrt(P/Q) lies strictly within the nearest grid cell.
 Exact proposition: With P>=0,Q>0,T>0,IZR t>=1,
 4*T²*P>(2t-1)²*Q and (2t+1)²*Q>4*T²*P imply
 cell(T,t,sqrt(P/Q)).
 Premises: Nonnegative variance; positive denominator and decimal scale;
 t is positive so the lower threshold is nonnegative.
 Method: The maintained real square-root-square identity and
 polynomial inequalities on positive quantities, without numerical sqrt.
 Library reuse: Stdlib.Reals.sqrt_pos, sqrt_sqrt, Stdlib.Psatz.nra.
 Boundary: The inequalities are strict and exclude halfway ties;
 no Gaussian conditional variance has been established here.
*)
Theorem report_sqrt_variance_certificate_sound :
  forall P Q T (t : Z),
    0 <= P -> 0 < Q -> 0 < T -> 1 <= IZR t ->
    0 < 4 * T * T * P -
      (2 * IZR t - 1) * (2 * IZR t - 1) * Q ->
    0 < (2 * IZR t + 1) * (2 * IZR t + 1) * Q -
      4 * T * T * P ->
    report_strict_rounding_interval T t (sqrt (P / Q)).
Proof.
  intros P Q T t HP HQ HT Ht Hlower Hupper.
  assert (Hquot : Q * (P / Q) = P).
  { field; lra. }
  assert (Hvariance : 0 <= P / Q) by nra.
  pose proof (sqrt_pos (P / Q)) as Hsqrtpositive.
  pose proof (sqrt_sqrt (P / Q) Hvariance) as Hsqr.
  assert (Hfactor : Q * (sqrt (P / Q) * sqrt (P / Q)) = P).
  { rewrite Hsqr; exact Hquot. }
  assert (Hscaled :
    (2 * T * sqrt (P / Q)) * (2 * T * sqrt (P / Q)) * Q =
    4 * T * T * P).
  { nra. }
  assert (HlowerSquares :
    (2 * IZR t - 1) * (2 * IZR t - 1) <
    (2 * T * sqrt (P / Q)) * (2 * T * sqrt (P / Q))).
  { apply (Rmult_lt_reg_r Q); [exact HQ |].
    rewrite Hscaled.
    nra. }
  assert (HupperSquares :
    (2 * T * sqrt (P / Q)) * (2 * T * sqrt (P / Q)) <
    (2 * IZR t + 1) * (2 * IZR t + 1)).
  { apply (Rmult_lt_reg_r Q); [exact HQ |].
    rewrite Hscaled.
    nra. }
  assert (HlowerNonnegative : 0 <= 2 * IZR t - 1) by lra.
  assert (HupperNonnegative : 0 <= 2 * IZR t + 1) by lra.
  assert (HscaledNonnegative : 0 <= 2 * T * sqrt (P / Q)) by nra.
  unfold report_strict_rounding_interval.
  split; nra.
Qed.

(**
 [report_mean_integer_certificate] (definition) — Integer numerator gap.
 Meaning: D_100=Q-2*abs(100*P-t*Q) for exact mean P/Q.
 Premises: To interpret as a rounding certificate, Q and 100 are positive.
 Method: Standard Z arithmetic; no floating-point evaluation.
 Library reuse: Stdlib.ZArith.Z.abs.
 Boundary: This is a candidate certificate; positivity is proved per row.
*)
Definition report_mean_integer_certificate (P Q t : Z) : Z :=
  (Q - 2 * Z.abs (100 * P - t * Q))%Z.

(**
 [report_sd_integer_lower] (definition) — Lower positive squared gap.
 Meaning: L_100=40000*P-(2*t-1)^2*Q for variance P/Q.
 Premises: Positive Q and positive t when used for rounding.
 Method: Direct integer expression mirroring the report.
 Library reuse: Stdlib.ZArith.Z.mul.
 Boundary: No square root is calculated here.
*)
Definition report_sd_integer_lower (P Q t : Z) : Z :=
  (40000 * P - (2 * t - 1) * (2 * t - 1) * Q)%Z.

(**
 [report_sd_integer_upper] (definition) — Upper positive squared gap.
 Meaning: U_100=(2*t+1)^2*Q-40000*P for variance P/Q.
 Premises: Positive Q and positive t when used for rounding.
 Method: Direct integer expression mirroring the report.
 Library reuse: Stdlib.ZArith.Z.mul.
 Boundary: No square root is calculated here.
*)
Definition report_sd_integer_upper (P Q t : Z) : Z :=
  ((2 * t + 1) * (2 * t + 1) * Q - 40000 * P)%Z.

(**
 [report_certificate_values] (definition) — Five exact table certificates.
 Meaning: The listed integer mean difference and lower/upper SD
 differences are collected for one IQ-150 report row.
 Exact representation: (D_mean,(L_pop,(U_pop,(L_cond,U_cond)))).
 Premises: Integer numerators, denominators and hundredth-grid indices.
 Method: Reuse the three separately defined integer certificate formulas.
 Library reuse: Stdlib.Init.Datatypes.prod and Stdlib.ZArith.
 Boundary: The returned integers are verified by individual kernel proofs.
*)
Definition report_certificate_values
    (mP mQ mt pP pQ pt cP cQ ct : Z) : Z * (Z * (Z * (Z * Z))) :=
  (report_mean_integer_certificate mP mQ mt,
   (report_sd_integer_lower pP pQ pt,
    (report_sd_integer_upper pP pQ pt,
     (report_sd_integer_lower cP cQ ct,
      report_sd_integer_upper cP cQ ct)))).


(** 
 [report_iq150_certificate_r1_k1] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=1 initial and k=1 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 1, 1511, 9225, 2399, 2401.
 Premises and side conditions: The exact mean is 140/1,
 population variance 180/1, conditional variance 36/1;
 the displayed hundredth indices are 14000, 1342, 600.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r1_k1 :
  report_certificate_values
    140 1 14000 180 1 1342 36 1 600 =
    (1, (1511, (9225, (2399, 2401)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r1_k2] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=1 initial and k=2 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 1, 239, 10041, 4375, 929.
 Premises and side conditions: The exact mean is 410/3,
 population variance 165/1, conditional variance 44/1;
 the displayed hundredth indices are 13667, 1285, 663.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r1_k2 :
  report_certificate_values
    410 3 13667 165 1 1285 44 1 663 =
    (1, (239, (10041, (4375, 929)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r1_k10] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=1 initial and k=10 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 7, 9061, 96275, 47871, 651025.
 Premises and side conditions: The exact mean is 1450/11,
 population variance 1575/11, conditional variance 6300/121;
 the displayed hundredth indices are 13182, 1197, 722.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r1_k10 :
  report_certificate_values
    1450 11 13182 1575 11 1197 6300 121 722 =
    (7, (9061, (96275, (47871, 651025)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r2_k1] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=2 initial and k=1 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 2, 239, 10041, 3676, 8196.
 Premises and side conditions: The exact mean is 875/6,
 population variance 165/1, conditional variance 55/4;
 the displayed hundredth indices are 14583, 1285, 371.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r2_k1 :
  report_certificate_values
    875 6 14583 165 1 1285 55 4 371 =
    (2, (239, (10041, (3676, 8196)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r2_k2] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=2 initial and k=2 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 4, 9838, 10242, 11696, 45136.
 Premises and side conditions: The exact mean is 575/4,
 population variance 315/2, conditional variance 315/16;
 the displayed hundredth indices are 14375, 1255, 444.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r2_k2 :
  report_certificate_values
    575 4 14375 315 2 1255 315 16 444 =
    (4, (9838, (10242, (11696, 45136)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r2_k10] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=2 initial and k=10 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 4, 4462, 14642, 25264, 44496.
 Premises and side conditions: The exact mean is 1675/12,
 population variance 285/2, conditional variance 475/16;
 the displayed hundredth indices are 13958, 1194, 545.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r2_k10 :
  report_certificate_values
    1675 12 13958 285 2 1194 475 16 545 =
    (4, (4462, (14642, (25264, 44496)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r3_k1] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=3 initial and k=1 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 5, 9838, 10242, 6100, 88236.
 Premises and side conditions: The exact mean is 1625/11,
 population variance 315/2, conditional variance 315/44;
 the displayed hundredth indices are 14773, 1255, 268.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r3_k1 :
  report_certificate_values
    1625 11 14773 315 2 1255 315 44 268 =
    (5, (9838, (10242, (6100, 88236)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r3_k2] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=3 initial and k=2 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 3, 4271, 5625, 11105, 135855.
 Premises and side conditions: The exact mean is 1610/11,
 population variance 153/1, conditional variance 612/55;
 the displayed hundredth indices are 14636, 1237, 334.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r3_k2 :
  report_certificate_values
    1610 11 14636 153 1 1237 612 55 334 =
    (3, (4271, (5625, (11105, 135855)))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** 
 [report_iq150_certificate_r3_k10] (theorem) — Exact integer certification of the
 published IQ-150 report row with r=3 initial and k=10 later scores.
 Mathematical meaning: The published mean and both standard deviation
 roundings have strictly positive, exactly computed integer gaps.
 Exact checked proposition: All five integer certificate values are
 57, 100907, 22957, 175221, 6457691.
 Premises and side conditions: The exact mean is 20450/143,
 population variance 1845/13, conditional variance 36900/1859;
 the displayed hundredth indices are 14301, 1191, 446.
 Proof/definition method: Rocq kernel-normalized Z arithmetic verifies
 the five displayed positive differences without a floating-point call.
 Library reuse: report_certificate_values, Z.abs, Stdlib.ZArith,
 and the Rocq kernel's definitional integer reduction.
 Boundary: This is a numerical arithmetic certificate of the printed
 report fractions, not a proof of Gaussian conditional expectations.
*)
Theorem report_iq150_certificate_r3_k10 :
  report_certificate_values
    20450 143 14301 1845 13 1191 36900 1859 446 =
    (57, (100907, (22957, (175221, 6457691)))).
Proof.
  vm_compute.
  reflexivity.
Qed.
