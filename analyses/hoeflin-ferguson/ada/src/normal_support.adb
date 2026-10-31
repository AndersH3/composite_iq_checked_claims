with Ada.Numerics.Long_Elementary_Functions;
with Interfaces.C;
package body Normal_Support is
   package Math renames Ada.Numerics.Long_Elementary_Functions;
   use type Interfaces.Unsigned_64;
   function C_Erfc (X : Interfaces.C.double) return Interfaces.C.double
     with Import, Convention => C, External_Name => "erfc";

   function Square_Root (X : Real) return Real is (Math.Sqrt (X));
   function Survival (X : Real) return Real is
     (0.5 * Real (C_Erfc (Interfaces.C.double (X / Math.Sqrt (2.0)))));

   function Inverse_Survival (P : Real) return Real is
      Lo : Real := -12.0;
      Hi : Real := 12.0;
      Mid : Real;
   begin
      if P <= 0.0 or else P >= 1.0 then
         raise Constraint_Error with "inverse survival requires 0 < P < 1";
      end if;
      if Survival (Lo) < P or else Survival (Hi) > P then
         raise Constraint_Error with "probability outside the supported inverse bracket";
      end if;
      for Iteration in 1 .. 100 loop
         Mid := Lo + (Hi - Lo) / 2.0;
         if Survival (Mid) > P then Lo := Mid; else Hi := Mid; end if;
      end loop;
      return Lo + (Hi - Lo) / 2.0;
   end Inverse_Survival;

   procedure Reset (G : out Generator; Seed : Interfaces.Unsigned_64) is
   begin
      G.State := Seed;
   end Reset;

   function Uniform (G : in out Generator) return Real is
      Bits : Interfaces.Unsigned_64;
   begin
      --  64-bit LCG state transition, followed by its top 52 bits.
      --  No claim of cryptographic randomness or exact independent sampling.
      G.State := G.State * 6_364_136_223_846_793_005 + 1_442_695_040_888_963_407;
      Bits := Interfaces.Shift_Right (G.State, 12);
      --  These midpoint grid values are exactly representable in binary64
      --  and lie strictly between zero and one, avoiding both endpoints.
      return (Real (Bits) + 0.5) * 2.0 ** (-52);
   end Uniform;

   procedure Normal_Pair (G : in out Generator; X, Y : out Real) is
      Radius : constant Real := Math.Sqrt (-2.0 * Math.Log (Uniform (G)));
      Angle : constant Real := 6.283185307179586476925286766559 * Uniform (G);
   begin
      X := Radius * Math.Cos (Angle);
      Y := Radius * Math.Sin (Angle);
   end Normal_Pair;
end Normal_Support;
