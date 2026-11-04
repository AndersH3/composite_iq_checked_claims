with Hoeflin_Core;
with Hoeflin_Boundary_Models;
with Interfaces;
package Normal_Support with SPARK_Mode is
   use type Interfaces.Unsigned_64;
   subtype Real is Hoeflin_Core.Real;
   subtype Probability is Real range 0.0 .. 1.0;
   subtype Bracket_Value is Real range -12.0 .. 12.0;
   subtype Unit_Root is Real range 0.0 .. 1.0;
   subtype Rare_Value is Real range 3.0 .. 10.0;
   subtype Normal_Value is Real range -9.0 .. 9.0;
   subtype Open_Unit is Real range 2.0 ** (-53) .. 1.0 - 2.0 ** (-53);

   --  The tiny C erfc, square-root, radius and quantile validation bodies
   --  are checked numerical boundaries. Their normal-return ranges are
   --  enforced at runtime; no approximation-error theorem is assumed.
   function Survival (X : Real) return Probability with
     Global => null,
     Post => (Survival'Result >= 0.0) and then
       (Survival'Result <= 1.0) and then
       (Hoeflin_Boundary_Models.Probability_Value (Survival'Result)),
     Depends => (Survival'Result => X);
   function Inverse_Survival (P : Real) return Bracket_Value with
     Global => null,
     Pre => P > 0.0 and then P < 1.0,
     Post => Inverse_Survival'Result in -12.0 .. 12.0,
     Depends => (Inverse_Survival'Result => P);
   function Square_Root (X : Real) return Real with
     Global => null,
     Post => Square_Root'Result >= 0.0
       and then (if X <= 1.0 then Square_Root'Result <= 1.0)
       and then (if X >= 1.0E-6 then Square_Root'Result >= 0.0005),
     Depends => (Square_Root'Result => X);

   function Rare_Quantile return Rare_Value with
     Global => null,
     Post => (Rare_Quantile'Result >= 3.0) and then
       (Rare_Quantile'Result <= 10.0) and then
       (Hoeflin_Boundary_Models.Rare_Quantile_Acceptable (Rare_Quantile'Result)),
     Depends => (Rare_Quantile'Result => null);

   --  Explicit state permits complete checked reset/recurrence contracts.
   type Generator is record
      State : Interfaces.Unsigned_64 := 20_261_030;
   end record;
   function State_Value (G : Generator) return Interfaces.Unsigned_64 with
     Global => null,
     Contract_Cases => (G.State = 0 => State_Value'Result = 0,
       G.State = Interfaces.Unsigned_64'Last => State_Value'Result = Interfaces.Unsigned_64'Last,
       others => State_Value'Result = G.State),
     Depends => (State_Value'Result => G);
   procedure Reset (G : out Generator; Seed : Interfaces.Unsigned_64) with
     Global => null,
     Post => State_Value (G) = Seed,
     Depends => (G => Seed),
     Contract_Cases => (Seed = 0 => G.State = 0, Seed = Interfaces.Unsigned_64'Last => G.State = Interfaces.Unsigned_64'Last, others => G.State = Seed);
   procedure Uniform (G : in out Generator; U : out Open_Unit) with
     Global => null,
     Post => (State_Value (G) = State_Value (G)'Old * 6_364_136_223_846_793_005 + 1_442_695_040_888_963_407) and then
       (U >= 2.0 ** (-53)) and then
       (U <= 1.0 - 2.0 ** (-53)),
     Depends => ((G, U) => G);
   procedure Normal_Pair (G : in out Generator; X, Y : out Normal_Value) with
     Global => null,
     Post => X >= -9.0 and then X <= 9.0 and then Y >= -9.0 and then Y <= 9.0,
     Depends => ((G, X, Y) => G);
end Normal_Support;
