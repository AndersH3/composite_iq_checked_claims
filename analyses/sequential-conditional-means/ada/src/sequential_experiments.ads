with Sequential_Core;

--  Executable floating-point refinements and bounded sample accumulation.
--
--  The exact formula coefficients live in Sequential_Core.  This package
--  makes the numerical boundary explicit: its contracts describe the Ada
--  floating-point operations, rather than claiming exact real division,
--  transcendental accuracy, normality of generated samples, or convergence
--  of a Monte Carlo estimate.  Square roots, random sampling, and output use
--  the existing standard-library boundary in the executable driver.
package Sequential_Experiments with SPARK_Mode is
   IQ_Origin : constant Long_Float := 100.0;
   IQ_SD     : constant Long_Float := 15.0;
   IQ_Variance : constant Long_Float := IQ_SD * IQ_SD;

   function Value (Q : Sequential_Core.Rational) return Long_Float with
     Global => null,
     Depends => (Value'Result => Q),
     Post =>
       Value'Result = Long_Float (Q.Num) / Long_Float (Q.Den)
       and then Value'Result in -1.0E19 .. 1.0E19
       and then (if Q.Num >= 0 then Value'Result >= 0.0)
       and then (if Q.Num <= 0 then Value'Result <= 0.0)
       and then (if Q.Num = 0 then Value'Result = 0.0);

   type Moment_Values is record
      Prediction, Mean : Long_Float;
      Population_Variance, Conditional_Variance : Long_Float;
      IQ_Prediction, IQ_Mean : Long_Float;
      IQ_Population_Variance, IQ_Conditional_Variance : Long_Float;
   end record;

   --  A is a standardized score, so the report's IQ 150 example supplies
   --  (150 - IQ_Origin) / IQ_SD.  Variances scale by IQ_SD squared, whereas
   --  means use the affine conversion IQ_Origin + IQ_SD * z.
   function From_Coefficients
     (F : Sequential_Core.Formula_Values; A : Long_Float)
      return Moment_Values with
     Global => null,
     Depends => (From_Coefficients'Result => (F, A)),
     Pre => A in -20.0 .. 20.0
       and then F.Population_Variance.Num >= 0
       and then F.Conditional_Variance.Num >= 0,
     Post =>
       From_Coefficients'Result.Prediction = Value (F.Prediction) * A
       and then From_Coefficients'Result.Mean = Value (F.Mean) * A
       and then From_Coefficients'Result.Population_Variance =
         Value (F.Population_Variance)
       and then From_Coefficients'Result.Conditional_Variance =
         Value (F.Conditional_Variance)
       and then From_Coefficients'Result.IQ_Prediction =
         IQ_Origin + IQ_SD * From_Coefficients'Result.Prediction
       and then From_Coefficients'Result.IQ_Mean =
         IQ_Origin + IQ_SD * From_Coefficients'Result.Mean
       and then From_Coefficients'Result.IQ_Population_Variance =
         IQ_Variance * From_Coefficients'Result.Population_Variance
       and then From_Coefficients'Result.IQ_Conditional_Variance =
         IQ_Variance * From_Coefficients'Result.Conditional_Variance
       and then From_Coefficients'Result.Population_Variance >= 0.0
       and then From_Coefficients'Result.Conditional_Variance >= 0.0
       and then From_Coefficients'Result.IQ_Population_Variance >= 0.0
       and then From_Coefficients'Result.IQ_Conditional_Variance >= 0.0
       and then (if A = 0.0 then
         From_Coefficients'Result.Prediction = 0.0 and then
         From_Coefficients'Result.Mean = 0.0);

   Max_Samples : constant := 1_000_000;
   Sample_Limit : constant Long_Float := 10_020.0;
   subtype Sample_Count is Natural range 0 .. Max_Samples;
   subtype Sum_Value is Long_Float range -2.0E10 .. 2.0E10;
   subtype Square_Sum_Value is Long_Float range 0.0 .. 2.0E14;
   type Accumulator is record
      Count : Sample_Count := 0;
      Sum : Sum_Value := 0.0;
      Sum_Squares : Square_Sum_Value := 0.0;
   end record;

   --  The public state exposes the observed numerical sums to the report.
   --  Reset followed by Add builds a sample; callers must not manufacture
   --  inconsistent state if they want the statistical interpretation of
   --  Finish.  Representability guards also protect arbitrary bounded state
   --  supplied by a caller, without assuming a hidden real-arithmetic sum.
   procedure Reset (Acc : out Accumulator) with
     Global => null,
     Depends => (Acc => null),
     Post => Acc.Count = 0
       and then Acc.Sum = 0.0
       and then Acc.Sum_Squares = 0.0;

   procedure Add (Acc : in out Accumulator; X : Long_Float) with
     Global => null,
     Depends => (Acc => (Acc, X)),
     Pre => X in -Sample_Limit .. Sample_Limit
       and then Acc.Count < Max_Samples
       and then Acc.Sum + X in Sum_Value
       and then Acc.Sum_Squares + X * X in Square_Sum_Value,
     Post => Acc.Count = Acc.Count'Old + 1
       and then Acc.Sum = Acc.Sum'Old + X
       and then Acc.Sum_Squares = Acc.Sum_Squares'Old + X * X
       and then Acc.Sum_Squares >= Acc.Sum_Squares'Old
       and then (if X >= 0.0 then Acc.Sum >= Acc.Sum'Old)
       and then (if X <= 0.0 then Acc.Sum <= Acc.Sum'Old)
       and then (if X = 0.0 then
         Acc.Sum = Acc.Sum'Old and then
         Acc.Sum_Squares = Acc.Sum_Squares'Old);

   type Empirical_Values is record
      Count : Sample_Count;
      Mean, Unbiased_Variance : Long_Float;
   end record;

   --  The ordinary sample-variance formula uses the (n-1) denominator.
   --  Cancellation can make its floating numerator slightly negative even
   --  for a correctly accumulated sample, so the numerical result is clamped
   --  at zero.  This guard is explicit in both implementation and contract;
   --  it is not a proof of statistical unbiasedness or numerical accuracy.
   function Finish (Acc : Accumulator) return Empirical_Values with
     Global => null,
     Depends => (Finish'Result => Acc),
     Pre => Acc.Count >= 2,
     Post => Finish'Result.Count = Acc.Count
       and then Finish'Result.Mean = Acc.Sum / Long_Float (Acc.Count)
       and then Finish'Result.Unbiased_Variance = Long_Float'Max
         (0.0, (Acc.Sum_Squares - Acc.Sum * Acc.Sum / Long_Float (Acc.Count)) /
          Long_Float (Acc.Count - 1))
       and then Finish'Result.Unbiased_Variance >= 0.0
       and then Finish'Result.Unbiased_Variance <= Square_Sum_Value'Last
       and then Finish'Result.Mean in -1.0E10 .. 1.0E10
       and then (if Acc.Sum >= 0.0 then Finish'Result.Mean >= 0.0)
       and then (if Acc.Sum <= 0.0 then Finish'Result.Mean <= 0.0)
       and then (if Acc.Sum = 0.0 then Finish'Result.Mean = 0.0);
end Sequential_Experiments;
