with Hoeflin_Core;
with Interfaces;
with Normal_Support;
package Report_IO with
  SPARK_Mode,
  Abstract_State => (Command_Input, Report_Output),
  Initializes => (Command_Input, Report_Output)
is
   use Hoeflin_Core;
   procedure Read_Simulation_Options
     (Trials : out Sample_Count; Seed : out Interfaces.Unsigned_64)
     with Global => (Input => Command_Input), Post => Trials >= 2;
   procedure Simulation_Header (Seed : Interfaces.Unsigned_64)
     with Global => (In_Out => Report_Output);
   procedure Simulation_Row
     (N : Test_Count; Trials : Sample_Count; Mean, Variance : Real;
      C : Tail_Counts; Rate_Two, Rate_Three, Expected_Two, Expected_Three : Normal_Support.Probability)
     with Global => (In_Out => Report_Output),
       Pre => Trials >= 2 and then Valid (C) and then C.Total = Trials;
   procedure Calculations_Header with Global => (In_Out => Report_Output);
   procedure Calculation_Row
     (N : Test_Count; Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value)
     with Global => (In_Out => Report_Output);
   procedure Infinite_Row
     (Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value)
     with Global => (In_Out => Report_Output);
   procedure Examples_Header with Global => (In_Out => Report_Output);
   procedure Example (Label : String; X : Real)
     with Global => (In_Out => Report_Output);
end Report_IO;
