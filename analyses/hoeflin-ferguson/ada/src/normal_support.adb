with Ada.Numerics.Long_Elementary_Functions;
with Interfaces.C;
with Hoeflin_Boundary_Models;
with Shared_Normal_Sampling;
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
      Hoeflin_Boundary_Models.Observe_Sqrt (X, Value);
      return Value;
   end Square_Root;

   function Survival (X : Real) return Probability
     with SPARK_Mode => Off
   is
      Raw : constant Real := Real (C_Erfc (Interfaces.C.double (X / Math.Sqrt (2.0))));
      Value : constant Long_Float := 0.5 * Raw;
   begin
      if not (Value >= 0.0 and then Value <= 1.0) then
         raise Constraint_Error with "erfc probability range failed";
      end if;
      Hoeflin_Boundary_Models.Observe_Erfc (Raw, Value);
      Hoeflin_Boundary_Models.Observe_Probability (Value);
      return Value;
   end Survival;

   procedure Check_Inverse_Bracket (P : Real; Lo, Hi : Bracket_Value) with
     Global => null,
     Pre => P > 0.0 and then P < 1.0,
     Post => Survival (Lo) >= P and then Survival (Hi) <= P,
     Depends => (null => (P, Lo, Hi));
   procedure Check_Inverse_Bracket (P : Real; Lo, Hi : Bracket_Value)
     with SPARK_Mode => Off
   is
      Lower_SF : constant Probability := Survival (Lo);
      Upper_SF : Probability;
   begin
      if Lower_SF < P then
         raise Constraint_Error with "probability outside the supported inverse bracket";
      end if;
      Upper_SF := Survival (Hi);
      if Upper_SF > P then
         raise Constraint_Error with "probability outside the supported inverse bracket";
      end if;
      Hoeflin_Boundary_Models.Observe_Inverse_Bracket
        (P, Lower_SF, Upper_SF);
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
      Hoeflin_Boundary_Models.Observe_Rare_Quantile (Value);
      return Value;
   end Rare_Quantile;

   --  Compatibility functions retain the report's established API while
   --  delegating all stochastic state transitions to the shared library.
   function State_Value (G : Generator) return Interfaces.Unsigned_64 is
     (Shared_Normal_Sampling.State_Value (G));

   procedure Reset (G : out Generator; Seed : Interfaces.Unsigned_64) is
   begin
      Shared_Normal_Sampling.Reset (G, Seed);
   end Reset;

   procedure Uniform (G : in out Generator; U : out Open_Unit) is
   begin
      Shared_Normal_Sampling.Uniform (G, U);
   end Uniform;

   procedure Normal_Pair (G : in out Generator; X, Y : out Normal_Value) is
   begin
      Shared_Normal_Sampling.Normal_Pair (G, X, Y);
   end Normal_Pair;
end Normal_Support;
