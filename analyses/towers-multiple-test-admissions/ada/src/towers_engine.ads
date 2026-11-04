with Admission_Core;
with Normal_Model;
package Towers_Engine with SPARK_Mode is
   subtype Case_Index is Positive range 1 .. 4;
   subtype Grid_Index is Positive range 1 .. 3;
   subtype Trial_Count is Admission_Core.Count range 1 .. Admission_Core.Max_Trials;
   subtype Seed_Value is Positive range 1 .. 2_147_483_646;
   type Real_Cases is array (Case_Index) of Long_Float;
   subtype Marginal_Probability is Normal_Model.Probability range 1.0E-5 .. 0.1;
   type Marginal_Cases is array (Case_Index) of Marginal_Probability;
   PA : constant Marginal_Cases := (0.02, 0.001, 1.0 / 33_000.0, 0.02);
   PB : constant Marginal_Cases := (0.02, 0.001, 1.0 / 33_000.0, 0.001);
   Rho : constant Normal_Model.Correlation := 0.7;
   type Calculation_Row is record
      A, B, Joint, Union_P, B_Given_A, A_Given_B, Phi, Refinement,
        Raw_Union, Raw_B_Given_A, Raw_A_Given_B : Long_Float := 0.0;
      Complement_A : Admission_Core.Probability_Units := 0;
   end record;
   type Calculation_Rows is array (Case_Index) of Calculation_Row;
   type Grid_Row is record
      Cutoff, Marginal, Joint, Conditional_P,
        Grid_Joint, Grid_Marginal, Grid_Conditional : Long_Float := 0.0;
   end record;
   type Grid_Rows is array (Grid_Index) of Grid_Row;
   type Simulation_Row is record
      Cells : Admission_Core.Counts;
      Marginal_A, Marginal_B, Union_N : Admission_Core.Count := 0;
      Joint_Fraction, Wilson_Lower, Wilson_Upper : Long_Float := 0.0;
      B_Given_A, A_Given_B : Long_Float := 0.0;
      Has_B_Given_A, Has_A_Given_B : Boolean := False;
   end record;
   type Simulation_Rows is array (Case_Index) of Simulation_Row;
   type Results is record
      Calculations : Calculation_Rows;
      Grid : Grid_Rows;
      Simulation : Simulation_Rows;
      Calibrated_Z, Calibrated_IQ, Calibrated_Marginal,
        Calibrated_Union : Long_Float := 0.0;
   end record;

   function Value (P : Admission_Core.Rational_Probability) return Normal_Model.Probability with
     Global => null,
     Pre => P.Denominator > 0 and P.Numerator <= P.Denominator,
     Post => (Value'Result >= 0.0) and then
       (Value'Result <= 1.0),
     Depends => (Value'Result => P);
   procedure Compute (Trials : Trial_Count; Seed : Seed_Value; Data : out Results) with
     Global => null,
     Post => ((for all K in Case_Index => Admission_Core.Total (Data.Simulation (K).Cells) = Trials)) and then
       ((for all K in Case_Index => Data.Simulation (K).Marginal_A = Admission_Core.Marginal_A (Data.Simulation (K).Cells))) and then
       ((for all K in Case_Index => Data.Simulation (K).Marginal_B = Admission_Core.Marginal_B (Data.Simulation (K).Cells))),
     Depends => (Data => (Trials, Seed));
end Towers_Engine;
