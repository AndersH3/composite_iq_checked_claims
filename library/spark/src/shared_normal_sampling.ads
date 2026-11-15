--  Shared deterministic normal sampling and checked square-root interface.
--
--  One canonical SPARK/Ada implementation serves Hoeflin/Ferguson and
--  Sequential; no report-specific package may be imported here.  The modular
--  recurrence is mathematically exact.  Transcendental/libm operations are
--  guarded trusted numerical boundaries, not probability-law proofs.
with Interfaces;
package Shared_Normal_Sampling with SPARK_Mode is
   use type Interfaces.Unsigned_64;
   subtype Real is Long_Float range -1.0E100 .. 1.0E100;
   subtype Open_Unit is Real range 2.0 ** (-53) .. 1.0 - 2.0 ** (-53);
   subtype Normal_Value is Real range -9.0 .. 9.0;
   subtype Variance is Real range 0.0 .. 4.0;
   subtype Root is Real range 0.0 .. 2.0;
   Multiplier : constant Interfaces.Unsigned_64 := 6_364_136_223_846_793_005;
   Increment : constant Interfaces.Unsigned_64 := 1_442_695_040_888_963_407;

   --  All generator state is explicit: a fixed seed gives a deterministic
   --  trajectory, with no global mutable state or cached spare normal.
   type Generator is record
      State : Interfaces.Unsigned_64 := 20_261_030;
   end record;

   --  Exact projection, including modular minimum and maximum.
   function State_Value (G : Generator) return Interfaces.Unsigned_64 with
     Global => null,
     Depends => (State_Value'Result => G),
     Contract_Cases =>
       (G.State = 0 => State_Value'Result = 0,
        G.State = Interfaces.Unsigned_64'Last =>
          State_Value'Result = Interfaces.Unsigned_64'Last,
        others => State_Value'Result = G.State);

   --  Reset from any 64-bit seed without depending on the previous state.
   procedure Reset (G : out Generator; Seed : Interfaces.Unsigned_64) with
     Global => null,
     Depends => (G => Seed),
     Post => State_Value (G) = Seed,
     Contract_Cases =>
       (Seed = 0 => G.State = 0,
        Seed = Interfaces.Unsigned_64'Last =>
          G.State = Interfaces.Unsigned_64'Last,
        others => G.State = Seed);

   --  Exactly one modular LCG step; the upper 52 state bits are mapped to
   --  an interior midpoint.  These properties do not assert randomness.
   procedure Uniform (G : in out Generator; U : out Open_Unit) with
     Global => null,
     Depends => ((G, U) => G),
     Post =>
       G.State = G.State'Old * Multiplier + Increment
       and then State_Value (G) =
         State_Value (G)'Old * Multiplier + Increment
       and then U >= Open_Unit'First
       and then U <= Open_Unit'Last
       and then U > 0.0
       and then U < 1.0
       and then (if G.State = 0 then U = 2.0 ** (-53))
       and then (if G.State = Interfaces.Unsigned_64'Last then
         U <= Open_Unit'Last);

   --  Checked bounded sqrt: every clause is enforced as a runtime acceptance
   --  condition, including special values and numerical residual.  Its
   --  implementation is explicitly excluded from automatic SPARK proof.
   function Checked_Sqrt (X : Variance) return Root with
     Global => null,
     Depends => (Checked_Sqrt'Result => X),
     Post =>
       Checked_Sqrt'Result >= 0.0
       and then Checked_Sqrt'Result <= 2.0
       and then (if X = 0.0 then Checked_Sqrt'Result = 0.0)
       and then (if X > 0.0 then Checked_Sqrt'Result > 0.0)
       and then (if X = 1.0 then Checked_Sqrt'Result = 1.0)
       and then (if X = 4.0 then Checked_Sqrt'Result = 2.0)
       and then (if X <= 1.0 then Checked_Sqrt'Result <= 1.0)
       and then (if X >= 1.0 then Checked_Sqrt'Result >= 1.0)
       and then (if X >= 1.0E-6 then Checked_Sqrt'Result >= 0.0005)
       and then abs (Checked_Sqrt'Result * Checked_Sqrt'Result - X)
         <= 1.0E-12;

   --  Two uniforms give exactly one Box--Muller pair.  The exact state
   --  recurrence and normal-result bounds are public obligations.
   procedure Normal_Pair
     (G : in out Generator; X, Y : out Normal_Value) with
     Global => null,
     Depends => ((G, X, Y) => G),
     Post =>
       X >= Normal_Value'First and then X <= Normal_Value'Last
       and then Y >= Normal_Value'First and then Y <= Normal_Value'Last
       and then G.State =
         (G.State'Old * Multiplier + Increment) * Multiplier + Increment;
end Shared_Normal_Sampling;
