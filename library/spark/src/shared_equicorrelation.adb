--  Shared exact arithmetic; one implementation and no report imports.
package body Shared_Equicorrelation with SPARK_Mode is
   function Numerator (N : Positive; C : Integer)
      return Long_Long_Integer is
   begin
      --  N-1 is nonnegative. N<=1e6 and |C|<=1000 bound every
      --  intermediate well below Long_Long_Integer'Last; no overflow.
      return Scale_1000 +
        Long_Long_Integer (C) * Long_Long_Integer (N - 1);
   end Numerator;
end Shared_Equicorrelation;
