package body Hoeflin_Core with SPARK_Mode is
   function Variance_Numerator
     (N : Test_Count; R : Correlation_Permille) return Numerator_Value
   is
      Loss : constant Long_Long_Integer :=
        Long_Long_Integer (1_000 - R) * Long_Long_Integer (N - 1);
      Result : constant Long_Long_Integer :=
        1_000 * Long_Long_Integer (N) - Loss;
   begin
      return Result;
   end Variance_Numerator;

   function Variance_Factor
     (N : Test_Count; R : Correlation_Permille) return Variance_Value
   is
      Num : constant Numerator_Value := Variance_Numerator (N, R);
      Den : constant Long_Long_Integer := 1_000 * Long_Long_Integer (N);
   begin
      return Real (Num) / Real (Den);
   end Variance_Factor;

   function Latent_Reliability
     (N : Test_Count; R : Correlation_Permille) return Real
   is
      Num : constant Long_Long_Integer :=
        Long_Long_Integer (N) * Long_Long_Integer (R);
      Den : constant Numerator_Value := Variance_Numerator (N, R);
   begin
      return Real (Num) / Real (Den);
   end Latent_Reliability;

   function Threshold (Quantile : Positive_Z; Scale : Scale_Value)
     return Positive_Z is
      Reduction : constant Real := Quantile * (1.0 - Scale);
   begin
      return Quantile - Reduction;
   end Threshold;

   function Composite (Mean_Z : Positive_Z; Scale : Scale_Value)
     return Composite_Z is
      Increase : constant Real := (Mean_Z * (1.0 - Scale)) / Scale;
   begin
      return Mean_Z + Increase;
   end Composite;

   function IQ (Z : Composite_Z) return IQ_Value is
   begin
      return 100.0 + 16.0 * Z;
   end IQ;

   procedure Observe (C : in out Tail_Counts; Z, Rare_Cutoff : Real) is
   begin
      C.Total := C.Total + 1;
      if Z > 2.0 then
         C.Above_Two := C.Above_Two + 1;
      end if;
      if Z > 3.0 then
         C.Above_Three := C.Above_Three + 1;
      end if;
      if Z > Rare_Cutoff then
         C.Above_Rare := C.Above_Rare + 1;
      end if;
   end Observe;
end Hoeflin_Core;
