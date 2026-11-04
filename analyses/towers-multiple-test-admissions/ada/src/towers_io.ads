with Admission_Core;
with Towers_IO_Models;
with Towers_Engine;
package Towers_IO with SPARK_Mode,
  Abstract_State => IO_State,
  Initializes => IO_State
is
   --  Explicit unproved system boundary. Bodies parse external arguments and
   --  format/write files; their exceptions and operating-system effects are
   --  not certified by the numerical/SPARK proof.
   function Read_Trials return Towers_Engine.Trial_Count with
     Global => (Input => IO_State),
     Post => (Read_Trials'Result >= 1) and then
       (Read_Trials'Result <= Admission_Core.Max_Trials) and then
       (Towers_IO_Models.Valid_Trials (Long_Long_Integer (Read_Trials'Result))),
     Depends => (Read_Trials'Result => IO_State);
   function Read_Seed return Towers_Engine.Seed_Value with
     Global => (Input => IO_State),
     Post => (Read_Seed'Result >= 1) and then
       (Read_Seed'Result <= 2_147_483_646) and then
       (Towers_IO_Models.Valid_Seed (Long_Long_Integer (Read_Seed'Result))),
     Depends => (Read_Seed'Result => IO_State);
   procedure Write_Report (Trials : Towers_Engine.Trial_Count;
                           Seed : Towers_Engine.Seed_Value;
                           Data : Towers_Engine.Results) with
     Global => (In_Out => IO_State),
     Pre => (for all K in Towers_Engine.Case_Index => Admission_Core.Total (Data.Simulation (K).Cells) = Trials) and then (for all K in Towers_Engine.Case_Index => Data.Simulation (K).Marginal_A = Admission_Core.Marginal_A (Data.Simulation (K).Cells)) and then (for all K in Towers_Engine.Case_Index => Data.Simulation (K).Marginal_B = Admission_Core.Marginal_B (Data.Simulation (K).Cells)),
     Depends => (IO_State => (Trials, Seed, Data, IO_State));
end Towers_IO;
