--  Single report-neutral LCG, Box--Muller, and sqrt implementation.
--  Its checked elementary-functions boundaries are deliberately distinct
--  from formal proofs of statistical normality or transcendental accuracy.
with Ada.Numerics.Long_Elementary_Functions;
with Interfaces;
package body Shared_Normal_Sampling with SPARK_Mode is
   package Math renames Ada.Numerics.Long_Elementary_Functions;
   use type Interfaces.Unsigned_64;

   --  The state projection is a pure expression, independent of report I/O.
   function State_Value (G : Generator) return Interfaces.Unsigned_64 is
     (G.State);

   --  The seed overwrites every prior generator state without side effects.
   procedure Reset (G : out Generator; Seed : Interfaces.Unsigned_64) is
   begin
      G.State := Seed;
   end Reset;

   --  Modulo-2**64 arithmetic is native to Unsigned_64; shifting right by
   --  12 supplies the exact high 52 bits consumed by both report families.
   procedure Uniform (G : in out Generator; U : out Open_Unit) is
      Bits : Interfaces.Unsigned_64;
   begin
      G.State := G.State * Multiplier + Increment;
      Bits := Interfaces.Shift_Right (G.State, 12);
      U := (Real (Bits) + 0.5) * 2.0 ** (-52);
   end Uniform;

   --  An external sqrt implementation must actually satisfy every promised
   --  bound (including NaN rejection) before the checked result is returned.
   function Checked_Sqrt (X : Variance) return Root
     with SPARK_Mode => Off
   is
      Value : constant Long_Float := Math.Sqrt (X);
   begin
      if not (Value >= 0.0 and then Value <= 2.0)
        or else (X = 0.0 and then Value /= 0.0)
        or else (X > 0.0 and then not (Value > 0.0))
        or else (X = 1.0 and then Value /= 1.0)
        or else (X = 4.0 and then Value /= 2.0)
        or else (X <= 1.0 and then Value > 1.0)
        or else (X >= 1.0 and then Value < 1.0)
        or else (X >= 1.0E-6 and then Value < 0.0005)
        or else not (abs (Value * Value - X) <= 1.0E-12)
      then
         raise Constraint_Error with "shared square-root acceptance failed";
      end if;
      return Root (Value);
   end Checked_Sqrt;

   subtype Radius_Value is Real range 0.0 .. 9.0;

   --  Box--Muller radius: checked log and sqrt bounds are executable,
   --  not proof axioms.  The 53-bit open interval rules out log(0).
   function Checked_Radius (U : Open_Unit) return Radius_Value with
     Global => null,
     Depends => (Checked_Radius'Result => U),
     Post => Checked_Radius'Result >= 0.0
       and then Checked_Radius'Result <= 9.0
       and then (if U = Open_Unit'Last then
         Checked_Radius'Result <= 9.0);
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

   --  Exactly two LCG transitions.  Sine/cosine come from Ada's standard
   --  elementary library; the bounded outputs retain runtime range checks.
   procedure Normal_Pair
     (G : in out Generator; X, Y : out Normal_Value) is
      U, V : Open_Unit;
      Radius : Radius_Value;
      Angle, Cosine, Sine : Real;
   begin
      Uniform (G, U);
      Uniform (G, V);
      Radius := Checked_Radius (U);
      Angle := 6.283185307179586476925286766559 * V;
      Cosine := Math.Cos (Angle);
      X := Radius * Cosine;
      Sine := Math.Sin (Angle);
      Y := Radius * Sine;
   end Normal_Pair;
end Shared_Normal_Sampling;
