--  Exact variance bookkeeping and bounded floating-point transformations.
package Hoeflin_Core with SPARK_Mode is
   subtype Real is Long_Float range -1.0E100 .. 1.0E100;
   subtype Test_Count is Positive range 1 .. 1_000_000;
   subtype Correlation_Permille is Natural range 0 .. 1_000;
   subtype Numerator_Value is Long_Long_Integer range 1_000 .. 1_000_000_000;
   subtype Variance_Value is Real range 1.0E-6 .. 1.0;
   subtype Scale_Value is Real range 0.0005 .. 1.0;
   subtype Positive_Z is Real range 0.0 .. 10.0;
   subtype Composite_Z is Real range 0.0 .. 20_000.0;
   subtype IQ_Value is Real range 100.0 .. 320_100.0;

   function Variance_Numerator
     (N : Test_Count; R : Correlation_Permille) return Numerator_Value
   with Global => null,
     Post => Variance_Numerator'Result =
       1_000 + Long_Long_Integer (R) * Long_Long_Integer (N - 1)
       and then Variance_Numerator'Result <= 1_000 * Long_Long_Integer (N);

   function Variance_Factor
     (N : Test_Count; R : Correlation_Permille) return Variance_Value
   with Global => null;

   function Latent_Reliability
     (N : Test_Count; R : Correlation_Permille) return Real
   with Global => null,
     Post => Latent_Reliability'Result in 0.0 .. 1.0;

   function Threshold (Quantile : Positive_Z; Scale : Scale_Value)
     return Positive_Z
   with Global => null,
     Post => Threshold'Result <= Quantile;

   function Composite (Mean_Z : Positive_Z; Scale : Scale_Value)
     return Composite_Z
   with Global => null,
     Post => Composite'Result >= Mean_Z;

   function IQ (Z : Composite_Z) return IQ_Value
   with Global => null;

   subtype Sample_Count is Natural range 0 .. 100_000_000;
   type Tail_Counts is record
      Total : Sample_Count := 0;
      Above_Two : Sample_Count := 0;
      Above_Three : Sample_Count := 0;
      Above_Rare : Sample_Count := 0;
   end record;

   function Valid (C : Tail_Counts) return Boolean is
     (C.Above_Rare <= C.Above_Three and then
      C.Above_Three <= C.Above_Two and then C.Above_Two <= C.Total)
   with Global => null;

   procedure Observe (C : in out Tail_Counts; Z, Rare_Cutoff : Real)
   with Global => null,
     Pre => Valid (C) and then C.Total < Sample_Count'Last
       and then Rare_Cutoff >= 3.0,
     Post => Valid (C) and then C.Total = C.Total'Old + 1
       and then C.Above_Two = C.Above_Two'Old + (if Z > 2.0 then 1 else 0)
       and then C.Above_Three = C.Above_Three'Old + (if Z > 3.0 then 1 else 0)
       and then C.Above_Rare = C.Above_Rare'Old + (if Z > Rare_Cutoff then 1 else 0);
end Hoeflin_Core;
