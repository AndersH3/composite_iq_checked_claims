with Ada.Numerics.Long_Elementary_Functions;
with Hoeflin_Boundary_Models;

package body Sequential_Sampling with SPARK_Mode is
   package Math renames Ada.Numerics.Long_Elementary_Functions;

   function Checked_Sqrt (X : Variance) return Root
     with SPARK_Mode => Off
   is
      Value : constant Long_Float := Math.Sqrt (X);
   begin
      --  Negated ordered comparisons also reject a NaN.  Keep this guard in
      --  ordinary executable code: the check must still run if assertions or
      --  ghost observations are disabled in a future compilation profile.
      if not (Value >= 0.0 and then Value <= 2.0)
        or else (X = 0.0 and then Value /= 0.0)
        or else (X > 0.0 and then not (Value > 0.0))
        or else (X = 1.0 and then Value /= 1.0)
        or else (X = 4.0 and then Value /= 2.0)
        or else (X <= 1.0 and then Value > 1.0)
        or else (X >= 1.0 and then Value < 1.0)
        or else not (abs (Value * Value - X) <= 1.0E-12)
        or else (X >= 1.0E-6 and then Value < 0.0005)
      then
         raise Constraint_Error with "sequential square-root acceptance failed";
      end if;

      --  Retain the repository's existing ghost observation of excluded sqrt
      --  implementations.  It records its established range acceptance only;
      --  the stronger endpoint and residual checks above remain explicit and
      --  are not presented as a formal proof of the library implementation.
      Hoeflin_Boundary_Models.Observe_Sqrt (X, Value);
      return Root (Value);
   end Checked_Sqrt;

   procedure Draw
     (G        : in out Normal_Support.Generator;
      Location : Location_Value;
      Sigma    : Sigma_Value;
      Sample   : out Sample_Value)
   is
      Noise, Unused_Noise : Normal_Support.Normal_Value;
   begin
      if Sigma = 0.0 then
         Sample := Location;
      else
         --  The second output belongs to the library's Box--Muller pair.  It
         --  is deliberately discarded rather than introducing hidden cached
         --  state; the explicit Generator contains all persistent draw state.
         Normal_Support.Normal_Pair (G, Noise, Unused_Noise);
         Sample := Location + Sigma * Noise;
      end if;
   end Draw;
end Sequential_Sampling;
