package Normal_Model with SPARK_Mode => Off is
   --  Explicit numerical boundary: libm erfc, elementary functions,
   --  quadrature accuracy and Gaussian assumptions are not SPARK theorems.
   function SF (Z : Long_Float) return Long_Float;
   function Inverse_SF (P : Long_Float) return Long_Float;
   function Joint_Tail
     (A, B, Rho : Long_Float; Steps : Positive := 20_000)
      return Long_Float;
   function Calibrated_OR_Cutoff
     (Target, Rho : Long_Float) return Long_Float;

   type Grid_Result is record
      Joint, Marginal : Long_Float;
   end record;
   type Grid_Results is array (1 .. 3) of Grid_Result;
   function Basic_Grid return Grid_Results;

   type Generator is limited private;
   procedure Reset (G : out Generator; Seed : Positive);
   procedure Normal_Pair (G : in out Generator; X, Y : out Long_Float);
private
   type Generator is limited record
      State : Long_Long_Integer := 1;
   end record;
end Normal_Model;
