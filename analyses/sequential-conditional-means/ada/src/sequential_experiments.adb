package body Sequential_Experiments with SPARK_Mode is
   function Value (Q : Sequential_Core.Rational) return Long_Float is
      --  Named finite ranges expose the conversion boundary to the prover.
      --  Even the largest signed integer numerator is below 10**19, and
      --  the exact rational denominator subtype starts at one.
      subtype Converted_Numerator is Long_Float range -1.0E19 .. 1.0E19;
      subtype Converted_Denominator is Long_Float range 1.0 .. 1.0E18;
      Num : constant Converted_Numerator := Long_Float (Q.Num);
      Den : constant Converted_Denominator := Long_Float (Q.Den);
      Result : constant Converted_Numerator := Num / Den;
   begin
      --  Convert once at this named boundary.  Keeping the exact numerator
      --  and denominator available in Sequential_Core avoids pretending
      --  that every decimal displayed by the driver is an exact rational.
      return Result;
   end Value;

   function From_Coefficients
     (F : Sequential_Core.Formula_Values; A : Long_Float)
      return Moment_Values
   is
      Prediction : constant Long_Float := Value (F.Prediction) * A;
      Mean : constant Long_Float := Value (F.Mean) * A;
      Population_Variance : constant Long_Float := Value (F.Population_Variance);
      Conditional_Variance : constant Long_Float := Value (F.Conditional_Variance);
   begin
      --  Reuse the converted standardized values in the affine IQ mapping.
      --  The two variance fields intentionally describe different sampling
      --  populations; neither is the variance of a deterministic prediction.
      return
        (Prediction => Prediction,
         Mean => Mean,
         Population_Variance => Population_Variance,
         Conditional_Variance => Conditional_Variance,
         IQ_Prediction => IQ_Origin + IQ_SD * Prediction,
         IQ_Mean => IQ_Origin + IQ_SD * Mean,
         IQ_Population_Variance => IQ_Variance * Population_Variance,
         IQ_Conditional_Variance => IQ_Variance * Conditional_Variance);
   end From_Coefficients;

   procedure Reset (Acc : out Accumulator) is
   begin
      --  Aggregate initialization prevents stale sums from surviving when a
      --  driver reuses the same accumulator for another simulation case.
      Acc := (Count => 0, Sum => 0.0, Sum_Squares => 0.0);
   end Reset;

   procedure Add (Acc : in out Accumulator; X : Long_Float) is
   begin
      --  This package stores just the statistics the report needs, without
      --  retaining a potentially large sample array or replacing the normal
      --  generator and elementary-function support already used by the repo.
      Acc.Count := Acc.Count + 1;
      Acc.Sum := Acc.Sum + X;
      Acc.Sum_Squares := Acc.Sum_Squares + X * X;
   end Add;

   function Finish (Acc : Accumulator) return Empirical_Values is
      subtype Sample_Divisor is Long_Float range 2.0 .. 1.0E6;
      subtype Variance_Divisor is Long_Float range 1.0 .. 1.0E6;
      subtype Correction_Value is Long_Float range 0.0 .. 2.0E20;
      subtype Centered_Value is Long_Float range -2.0E20 .. 2.0E14;
      N : constant Sample_Divisor := Long_Float (Acc.Count);
      NM1 : constant Variance_Divisor := Long_Float (Acc.Count - 1);
      Correction : constant Correction_Value := Acc.Sum * Acc.Sum / N;
      Centered : constant Centered_Value := Acc.Sum_Squares - Correction;
      Raw_Variance : constant Centered_Value := Centered / NM1;
      Variance : constant Square_Sum_Value :=
        Long_Float'Max (0.0, Raw_Variance);
   begin
      --  Ada's standard scalar Max performs the explicit cancellation guard;
      --  no custom square-root or statistical library is introduced here.
      return
        (Count => Acc.Count,
         Mean => Acc.Sum / N,
         Unbiased_Variance => Variance);
   end Finish;
end Sequential_Experiments;
