with Ada.Numerics.Long_Elementary_Functions;
with Ada.Numerics;
with Interfaces.C;

package body Normal_Model with SPARK_Mode => Off is
   use Ada.Numerics.Long_Elementary_Functions;
   Pi : constant Long_Float := Ada.Numerics.Pi;
   function C_Erfc (X : Interfaces.C.double) return Interfaces.C.double
     with Import, Convention => C, External_Name => "erfc";

   function SF (Z : Long_Float) return Long_Float is
     (0.5 * Long_Float (C_Erfc (Interfaces.C.double (Z / Sqrt (2.0)))));

   function Inverse_SF (P : Long_Float) return Long_Float is
      Lo : Long_Float := -12.0;
      Hi : Long_Float := 12.0;
      Mid : Long_Float;
   begin
      if P <= SF (Hi) or else P >= SF (Lo) then
         raise Constraint_Error with "inverse SF probability outside [-12,12] bracket";
      end if;
      for Iteration in 1 .. 80 loop
         Mid := (Lo + Hi) / 2.0;
         if SF (Mid) > P then
            Lo := Mid;
         else
            Hi := Mid;
         end if;
      end loop;
      return (Lo + Hi) / 2.0;
   end Inverse_SF;

   function Joint_Tail
     (A, B, Rho : Long_Float; Steps : Positive := 20_000)
      return Long_Float
   is
      function Density (R : Long_Float) return Long_Float is
         S : constant Long_Float := 1.0 - R * R;
      begin
         return Exp (-(A * A - 2.0 * R * A * B + B * B) / (2.0 * S))
           / (2.0 * Pi * Sqrt (S));
      end Density;
      H, Sum : Long_Float;
   begin
      if Rho < 0.0 or else Rho > 0.95 or else Steps mod 2 /= 0 then
         raise Constraint_Error with "joint tail requires 0<=rho<=.95 and even steps";
      end if;
      H := Rho / Long_Float (Steps);
      Sum := Density (0.0) + Density (Rho);
      for I in 1 .. Steps - 1 loop
         Sum := Sum + (if I mod 2 = 0 then 2.0 else 4.0)
           * Density (Long_Float (I) * H);
      end loop;
      return SF (A) * SF (B) + H * Sum / 3.0;
   end Joint_Tail;

   function Calibrated_OR_Cutoff
     (Target, Rho : Long_Float) return Long_Float
   is
      Lo : Long_Float := 0.0;
      Hi : Long_Float := 8.0;
      Mid, Union_P : Long_Float;
   begin
      if Target <= 0.0 or else Target >= 0.5 then
         raise Constraint_Error with "OR target outside supported interval";
      end if;
      for I in 1 .. 65 loop
         Mid := (Lo + Hi) / 2.0;
         Union_P := 2.0 * SF (Mid) - Joint_Tail (Mid, Mid, Rho, 2_000);
         if Union_P > Target then Lo := Mid; else Hi := Mid; end if;
      end loop;
      return (Lo + Hi) / 2.0;
   end Calibrated_OR_Cutoff;

   function Basic_Grid return Grid_Results is
      Cutoffs : constant array (1 .. 3) of Long_Float := (133.0, 150.0, 164.0);
      Result : Grid_Results := (others => (Joint => 0.0, Marginal => 0.0));
      X, Y, ZX, ZY, D : Long_Float;
      Total : Long_Float := 0.0;
      R : constant Long_Float := 0.7;
   begin
      for I in 0 .. 396 loop
         X := 1.0 + 0.5 * Long_Float (I);
         ZX := (X - 100.0) / 16.0;
         for J in 0 .. 396 loop
            Y := 1.0 + 0.5 * Long_Float (J);
            ZY := (Y - 100.0) / 16.0;
            D := Exp (-(ZX * ZX - 2.0 * R * ZX * ZY + ZY * ZY)
                      / (2.0 * (1.0 - R * R)))
              / (2.0 * Pi * Sqrt (1.0 - R * R));
            Total := Total + D;
            for K in Cutoffs'Range loop
               if X >= Cutoffs (K) then
                  Result (K).Marginal := Result (K).Marginal + D;
                  if Y >= Cutoffs (K) then
                     Result (K).Joint := Result (K).Joint + D;
                  end if;
               end if;
            end loop;
         end loop;
      end loop;
      for K in Result'Range loop
         Result (K).Joint := Result (K).Joint / Total;
         Result (K).Marginal := Result (K).Marginal / Total;
      end loop;
      return Result;
   end Basic_Grid;

   procedure Reset (G : out Generator; Seed : Positive) is
   begin
      if Seed >= 2_147_483_647 then
         raise Constraint_Error with "seed must be in 1..2147483646";
      end if;
      G.State := Long_Long_Integer (Seed);
   end Reset;

   function Uniform (G : in out Generator) return Long_Float is
   begin
      --  Park-Miller multiplicative generator; exact integer recurrence.
      G.State := (48_271 * G.State) mod 2_147_483_647;
      return Long_Float (G.State) / 2_147_483_647.0;
   end Uniform;

   procedure Normal_Pair (G : in out Generator; X, Y : out Long_Float) is
      U : constant Long_Float := Uniform (G);
      V : constant Long_Float := Uniform (G);
      Radius : constant Long_Float := Sqrt (-2.0 * Log (U));
      Angle : constant Long_Float := 2.0 * Pi * V;
   begin
      X := Radius * Cos (Angle);
      Y := Radius * Sin (Angle);
   end Normal_Pair;
end Normal_Model;
