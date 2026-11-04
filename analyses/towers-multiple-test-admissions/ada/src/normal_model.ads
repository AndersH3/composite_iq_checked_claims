package Normal_Model with SPARK_Mode is
   --  Numerical algorithms are analyzed in SPARK. Accuracy of elementary
   --  functions/libm, quadrature error and Gaussian assumptions are separate
   --  numerical/model boundaries, not consequences of range/flow proofs.
   subtype Z_Value is Long_Float range -12.0 .. 12.0;
   subtype Probability is Long_Float range 0.0 .. 1.0;
   subtype Correlation is Long_Float range 0.0 .. 0.95;
   subtype Normal_Value is Long_Float range -8.0 .. 8.0;
   function Square_Root (X : Long_Float) return Long_Float with
     Global => null,
     Pre => X in 0.0 .. 1.0E6,
     Post => Square_Root'Result in 0.0 .. 1.0E3
       and (if X >= 1.0E-30 then Square_Root'Result >= 1.0E-15)
       and (if X >= 0.0625 then Square_Root'Result >= 0.25)
       and (if X >= 1.0 then Square_Root'Result >= 1.0)
       and (if X <= 1.0 then Square_Root'Result <= 1.0)
       and (if X <= 4.0 then Square_Root'Result <= 2.0)
       and (if X <= 64.0 then Square_Root'Result <= 8.0),
     Depends => (Square_Root'Result => X);
   function SF (Z : Long_Float) return Probability with
     Global => null,
     Post => (if Z >= 10.0 then SF'Result < 1.0E-20) and then
       (if Z <= -10.0 then SF'Result > 1.0 - 1.0E-14) and then
       (SF'Result in 0.0 .. 1.0),
     Depends => (SF'Result => Z);
   function Inverse_SF (P : Probability) return Z_Value with
     Global => null,
     Pre => P > SF (12.0) and P < SF (-12.0),
     Post => (Inverse_SF'Result in -12.0 .. 12.0),
     Depends => (Inverse_SF'Result => P);
   function Joint_Tail
     (A, B : Long_Float; Rho : Correlation; Steps : Positive := 20_000)
      return Probability with
     Global => null,
     Pre => Steps mod 2 = 0
       and abs (A) <= 1.0E100 and abs (B) <= 1.0E100,
     Post => (Joint_Tail'Result >= 0.0) and then
       (Joint_Tail'Result <= 1.0),
     Depends => (Joint_Tail'Result => (A, B, Rho, Steps));
   function Calibrated_OR_Cutoff
     (Target : Probability; Rho : Correlation) return Z_Value with
     Global => null,
     Pre => Target > 0.0 and Target < 0.5,
     Post => Calibrated_OR_Cutoff'Result in 0.0 .. 8.0,
     Depends => (Calibrated_OR_Cutoff'Result => (Target, Rho));

   type Grid_Result is record
      Joint, Marginal : Probability;
   end record;
   type Grid_Results is array (1 .. 3) of Grid_Result;
   function Basic_Grid return Grid_Results with
     Global => null,
     Post => ((for all K in Basic_Grid'Result'Range => Basic_Grid'Result (K).Joint >= 0.0)) and then
       ((for all K in Basic_Grid'Result'Range => Basic_Grid'Result (K).Joint <= 1.0)) and then
       ((for all K in Basic_Grid'Result'Range => Basic_Grid'Result (K).Marginal in 0.0 .. 1.0)),
     Depends => (Basic_Grid'Result => null);

   --  Explicit state permits complete checked reset/recurrence contracts.
   subtype State_Value is Long_Long_Integer range 1 .. 2_147_483_646;
   type Generator is limited record
      State : State_Value := 1;
   end record;
   procedure Reset (G : out Generator; Seed : Positive) with
     Global => null,
     Pre => Seed < 2_147_483_647,
     Post => G.State = State_Value (Seed) and then G.State >= 1,
     Depends => (G => Seed);
   procedure Normal_Pair (G : in out Generator; X, Y : out Normal_Value) with
     Global => null,
     Post => X >= -8.0 and then X <= 8.0 and then Y >= -8.0 and then Y <= 8.0,
     Depends => ((G, X, Y) => G);
end Normal_Model;
