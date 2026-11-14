--  Exact arithmetic for the finite and asymptotic formulas in the paper.
--
--  Correlations are supplied in signed permille.  The pair (Num, Den) is an
--  unreduced exact rational value, not a home-grown rational-arithmetic API:
--  the core only constructs formula coefficients, and uses Ada's integer
--  arithmetic.  Conversion, square roots, and formatted I/O belong to the
--  separately documented numerical boundary.  No transcendental backend or
--  random-number generator is trusted by this package.
package Sequential_Core with SPARK_Mode is
   Scale     : constant Long_Long_Integer := 1_000;
   Max_Total : constant := 1_000;
   subtype Count is Positive range 1 .. Max_Total;
   subtype Correlation_Permille is Integer range -1_000 .. 1_000;

   --  The largest constructed denominator is at most 10**15.  The wider
   --  representable bound leaves room for clients without weakening the
   --  exact formula contracts.  Numerators may be signed (negative finite
   --  correlations give a negative subsequent prediction coefficient).
   subtype Denominator_Value is Long_Long_Integer range
     1 .. 1_000_000_000_000_000_000;
   type Rational is record
      Num : Long_Long_Integer := 0;
      Den : Denominator_Value := 1;
   end record;

   function D_Numerator
     (N : Count; C : Correlation_Permille) return Long_Long_Integer with
     Global => null,
     Depends => (D_Numerator'Result => (N, C)),
     Post =>
       D_Numerator'Result = Scale + Long_Long_Integer (C) *
         Long_Long_Integer (N - 1)
       and then D_Numerator'Result >= Scale * (2 - Long_Long_Integer (N))
       and then D_Numerator'Result <= Scale * Long_Long_Integer (N)
       and then (if N = 1 then D_Numerator'Result = Scale)
       and then (if C = 0 then D_Numerator'Result = Scale)
       and then (if C = 1_000 then
         D_Numerator'Result = Scale * Long_Long_Integer (N))
       and then (if C = -1_000 then
         D_Numerator'Result = Scale * (2 - Long_Long_Integer (N)))
       and then (if C >= 0 then D_Numerator'Result >= Scale)
       and then (if C <= 0 then D_Numerator'Result <= Scale);

   --  Valid explicitly checks the full covariance eigenvalue, the initial
   --  block denominator, and the next-prefix eigenvalue.  The last check is
   --  mathematically implied by the full-battery domain but makes the exact
   --  nonnegative residual-variance obligation visible to executable callers
   --  and the prover.  It does not silently accept an invalid covariance.
   function Valid
     (R, K : Count; C : Correlation_Permille) return Boolean is
     (R + K <= Max_Total and then
      D_Numerator (Count (R + K), C) >= 0 and then
      D_Numerator (R, C) > 0 and then
      D_Numerator (R, C) + Long_Long_Integer (C) >= 0)
     with
     Global => null,
     Depends => (Valid'Result => (R, K, C)),
     Post =>
       Valid'Result =
         (R + K <= Max_Total and then
          D_Numerator (Count (R + K), C) >= 0 and then
          D_Numerator (R, C) > 0 and then
          D_Numerator (R, C) + Long_Long_Integer (C) >= 0)
       and then (if Valid'Result then R + K <= Max_Total)
       and then (if Valid'Result then
         D_Numerator (Count (R + K), C) >= 0)
       and then (if Valid'Result then D_Numerator (R, C) > 0)
       and then (if Valid'Result then
         D_Numerator (R, C) + Long_Long_Integer (C) >= 0)
       and then (if R + K > Max_Total then not Valid'Result)
       and then (if R + K <= Max_Total and then
         D_Numerator (Count (R + K), C) < 0 then not Valid'Result)
       and then (if R + K <= Max_Total and then C >= 0 then
         Valid'Result);

   type Formula_Values is record
      --  Coefficients multiply the standardized starting score a.  Mean
      --  includes all R observed starting values and K later predictions.
      Prediction, Mean : Rational;
      Population_Variance, Conditional_Variance : Rational;
      --  Regression_Coefficient multiplies the SUM of the R initial scores.
      --  Residual_Variance is the next test's variance given that block.
      Regression_Coefficient, Residual_Variance : Rational;
      Common_Eigenvalue, Contrast_Eigenvalue : Rational;
      --  Has_Inverse concerns the R-by-R starting block.  R=1 has inverse
      --  [1] even at c=1.  With R>1 and c=1 the covariance is singular and
      --  the two inverse fields are explicit zero/one placeholders.
      Has_Inverse : Boolean;
      Inverse_Diagonal, Inverse_Off_Diagonal : Rational;
   end record;

   function Calculate
     (R, K : Count; C : Correlation_Permille) return Formula_Values with
     Global => null,
     Depends => (Calculate'Result => (R, K, C)),
     Pre => Valid (R, K, C),
     Post =>
       Calculate'Result.Prediction.Num = Long_Long_Integer (R) * Long_Long_Integer (C)
       and then Calculate'Result.Prediction.Den = D_Numerator (R, C)
       and then Calculate'Result.Mean.Num = Long_Long_Integer (R) *
         D_Numerator (Count (R + K), C)
       and then Calculate'Result.Mean.Den = Long_Long_Integer (R + K) *
         D_Numerator (R, C)
       and then Calculate'Result.Population_Variance.Num =
         D_Numerator (Count (R + K), C)
       and then Calculate'Result.Population_Variance.Den =
         Scale * Long_Long_Integer (R + K)
       and then Calculate'Result.Conditional_Variance.Num =
         Long_Long_Integer (K) * (Scale - Long_Long_Integer (C)) *
         D_Numerator (Count (R + K), C)
       and then Calculate'Result.Conditional_Variance.Den =
         Scale * Long_Long_Integer (R + K) * Long_Long_Integer (R + K) *
         D_Numerator (R, C)
       and then Calculate'Result.Regression_Coefficient.Num = Long_Long_Integer (C)
       and then Calculate'Result.Regression_Coefficient.Den = D_Numerator (R, C)
       and then Calculate'Result.Residual_Variance.Num =
         (Scale - Long_Long_Integer (C)) *
         (D_Numerator (R, C) + Long_Long_Integer (C))
       and then Calculate'Result.Residual_Variance.Den = Scale * D_Numerator (R, C)
       and then Calculate'Result.Common_Eigenvalue.Num =
         D_Numerator (Count (R + K), C)
       and then Calculate'Result.Common_Eigenvalue.Den = Scale
       and then Calculate'Result.Contrast_Eigenvalue.Num = Scale - Long_Long_Integer (C)
       and then Calculate'Result.Contrast_Eigenvalue.Den = Scale
       and then Calculate'Result.Mean.Num >= 0
       and then Calculate'Result.Population_Variance.Num >= 0
       and then Calculate'Result.Conditional_Variance.Num >= 0
       and then Calculate'Result.Residual_Variance.Num >= 0
       and then Calculate'Result.Has_Inverse = (R = 1 or else C < 1_000)
       and then (if R = 1 then
         Calculate'Result.Inverse_Diagonal.Num = 1 and then
         Calculate'Result.Inverse_Diagonal.Den = 1 and then
         Calculate'Result.Inverse_Off_Diagonal.Num = 0 and then
         Calculate'Result.Inverse_Off_Diagonal.Den = 1)
       and then (if R > 1 and then C < 1_000 then
         Calculate'Result.Inverse_Diagonal.Num =
           Scale * (D_Numerator (R, C) - Long_Long_Integer (C)) and then
         Calculate'Result.Inverse_Diagonal.Den =
           (Scale - Long_Long_Integer (C)) * D_Numerator (R, C) and then
         Calculate'Result.Inverse_Off_Diagonal.Num = -Scale * Long_Long_Integer (C) and then
         Calculate'Result.Inverse_Off_Diagonal.Den =
           (Scale - Long_Long_Integer (C)) * D_Numerator (R, C))
       and then (if not Calculate'Result.Has_Inverse then
         Calculate'Result.Inverse_Diagonal.Num = 0 and then
         Calculate'Result.Inverse_Diagonal.Den = 1 and then
         Calculate'Result.Inverse_Off_Diagonal.Num = 0 and then
         Calculate'Result.Inverse_Off_Diagonal.Den = 1);

   type Limit_Values is record
      Prediction, Mean : Rational;
      Population_Variance, Conditional_Variance : Rational;
   end record;

   --  A fixed negative correlation cannot remain admissible as K grows
   --  without bound.  The nonnegative-c precondition is therefore a model
   --  domain requirement, not a convenient restriction of finite cases.
   function Limits
     (R : Count; C : Correlation_Permille) return Limit_Values with
     Global => null,
     Depends => (Limits'Result => (R, C)),
     Pre => C >= 0,
     Post =>
       Limits'Result.Prediction.Num = Long_Long_Integer (R) * Long_Long_Integer (C)
       and then Limits'Result.Prediction.Den = D_Numerator (R, C)
       and then Limits'Result.Mean.Num = Limits'Result.Prediction.Num
       and then Limits'Result.Mean.Den = Limits'Result.Prediction.Den
       and then Limits'Result.Population_Variance.Num = Long_Long_Integer (C)
       and then Limits'Result.Population_Variance.Den = Scale
       and then Limits'Result.Conditional_Variance.Num =
         Long_Long_Integer (C) * (Scale - Long_Long_Integer (C))
       and then Limits'Result.Conditional_Variance.Den = Scale * D_Numerator (R, C)
       and then Limits'Result.Prediction.Num >= 0
       and then Limits'Result.Population_Variance.Num >= 0
       and then Limits'Result.Conditional_Variance.Num >= 0
       and then (if C = 0 then Limits'Result.Mean.Num = 0)
       and then (if C = 1_000 then
         Limits'Result.Mean.Num = Limits'Result.Mean.Den)
       and then (if C = 0 or else C = 1_000 then
         Limits'Result.Conditional_Variance.Num = 0);
end Sequential_Core;
