with Hoeflin_Core;
with Interfaces;
package Normal_Support with SPARK_Mode => Off is
   subtype Real is Hoeflin_Core.Real;
   function Survival (X : Real) return Real;
   function Inverse_Survival (P : Real) return Real;
   function Square_Root (X : Real) return Real;
   type Generator is private;
   procedure Reset (G : out Generator; Seed : Interfaces.Unsigned_64);
   procedure Normal_Pair (G : in out Generator; X, Y : out Real);
private
   type Generator is record
      State : Interfaces.Unsigned_64 := 20_261_030;
   end record;
end Normal_Support;
