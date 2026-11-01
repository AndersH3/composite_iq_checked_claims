with Ada.Numerics.Long_Elementary_Functions;
with Interfaces.C;
package body Normal_Support with SPARK_Mode is
   package Math renames Ada.Numerics.Long_Elementary_Functions;
   use type Interfaces.Unsigned_64;
   function C_Erfc (X : Interfaces.C.double) return Interfaces.C.double
     with Import, Convention => C, External_Name => "erfc", SPARK_Mode => Off;

   function Square_Root (X : Real) return Real
     with SPARK_Mode => Off
   is
      Value : constant Long_Float := Math.Sqrt (X);
   begin
      if not (Value >= 0.0 and then Value <= Real'Last) or else
        (X <= 1.0 and then Value > 1.0) or else
        (X >= 1.0E-6 and then Value < 0.0005)
      then
         raise Constraint_Error with "square-root range contract failed";
      end if;
      return Value;
   end Square_Root;

   function Survival (X : Real) return Probability
     with SPARK_Mode => Off
   is
      Value : constant Long_Float :=
        0.5 * Real (C_Erfc (Interfaces.C.double (X / Math.Sqrt (2.0))));
   begin
      if not (Value >= 0.0 and then Value <= 1.0) then
         raise Constraint_Error with "erfc probability range failed";
      end if;
      return Value;
   end Survival;

   procedure Check_Inverse_Bracket (P : Real; Lo, Hi : Bracket_Value)
     with Global => null;
   procedure Check_Inverse_Bracket (P : Real; Lo, Hi : Bracket_Value)
     with SPARK_Mode => Off is
   begin
      if Survival (Lo) < P or else Survival (Hi) > P then
         raise Constraint_Error with "probability outside the supported inverse bracket";
      end if;
   end Check_Inverse_Bracket;

   function Inverse_Survival (P : Real) return Bracket_Value is
      Lo : Bracket_Value := -12.0;
      Hi : Bracket_Value := 12.0;
      Mid : Bracket_Value;
   begin
      Check_Inverse_Bracket (P, Lo, Hi);
      for Iteration in 1 .. 100 loop
         pragma Loop_Invariant (Lo <= Hi);
         Mid := Lo + (Hi - Lo) / 2.0;
         if Survival (Mid) > P then Lo := Mid; else Hi := Mid; end if;
      end loop;
      return Lo + (Hi - Lo) / 2.0;
   end Inverse_Survival;

   function Rare_Quantile return Rare_Value with SPARK_Mode => Off is
      Value : constant Real := Inverse_Survival (1.0E-6);
   begin
      if not (Value >= 3.0 and then Value <= 10.0) then
         raise Constraint_Error with "normal quantile outside supported rare range";
      end if;
      return Value;
   end Rare_Quantile;

   function State_Value (G : Generator) return Interfaces.Unsigned_64 is (G.State);

   procedure Reset (G : out Generator; Seed : Interfaces.Unsigned_64) is
   begin
      G.State := Seed;
   end Reset;

   procedure Uniform (G : in out Generator; U : out Open_Unit) is
      Bits : Interfaces.Unsigned_64;
   begin
      G.State := G.State * 6_364_136_223_846_793_005 + 1_442_695_040_888_963_407;
      Bits := Interfaces.Shift_Right (G.State, 12);
      U := (Real (Bits) + 0.5) * 2.0 ** (-52);
   end Uniform;

   subtype Radius_Value is Real range 0.0 .. 9.0;
   function Checked_Radius (U : Open_Unit) return Radius_Value
     with Global => null;
   function Checked_Radius (U : Open_Unit) return Radius_Value
     with SPARK_Mode => Off
   is
      Log_U : constant Long_Float := Math.Log (U);
      Value : Long_Float;
   begin
      if not (Log_U >= -38.0 and then Log_U <= 0.0) then
         raise Constraint_Error with "logarithm range contract failed";
      end if;
      Value := Math.Sqrt (-2.0 * Log_U);
      if not (Value >= 0.0 and then Value <= 9.0) then
         raise Constraint_Error with "normal radius range contract failed";
      end if;
      return Value;
   end Checked_Radius;

   procedure Normal_Pair (G : in out Generator; X, Y : out Normal_Value) is
      U, V : Open_Unit;
      Radius : Radius_Value;
      Angle : Real;
   begin
      Uniform (G, U);
      Uniform (G, V);
      Radius := Checked_Radius (U);
      Angle := 6.283185307179586476925286766559 * V;
      X := Radius * Math.Cos (Angle);
      Y := Radius * Math.Sin (Angle);
   end Normal_Pair;
end Normal_Support;
