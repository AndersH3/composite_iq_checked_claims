with Hoeflin_Core;
with Hoeflin_Boundary_Models;
with Interfaces;
with Normal_Support;
package Report_IO with
  SPARK_Mode,
  Abstract_State => (Command_Input, Report_Output),
  Initializes => (Command_Input, Report_Output, Trace)
is
   use Hoeflin_Core;
   use type Hoeflin_Boundary_Models.Event_Count;
   use type Hoeflin_Boundary_Models.Event_Kind;
   use type Hoeflin_Boundary_Models.Section_Kind;
   use type Hoeflin_Boundary_Models.Report_Trace;
   --  Normal-return request state, distinct from physical I/O certification.
   Trace : Hoeflin_Boundary_Models.Report_Trace :=
     Hoeflin_Boundary_Models.Empty_Trace;
   procedure Read_Simulation_Options
     (Trials : out Sample_Count; Seed : out Interfaces.Unsigned_64) with
     Global => (Input => Command_Input, In_Out => Trace),
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Options_Read, Hoeflin_Boundary_Models.Options_Payload (Trials, Seed)) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Options_Read and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trials >= 2,
     Depends => ((Trials, Seed, Trace) => (Command_Input, Trace));
   procedure Simulation_Header (Seed : Interfaces.Unsigned_64) with
     Global => (In_Out => (Report_Output, Trace)),
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Simulation_Header_Event, Hoeflin_Boundary_Models.Options_Payload (0, Seed)) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Simulation_Header_Event and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trace.Rows = 0,
     Depends => ((Report_Output, Trace) => (Seed, Report_Output, Trace));
   procedure Simulation_Row
     (N : Test_Count; Trials : Sample_Count; Mean, Variance : Real;
      C : Tail_Counts; Rate_Two, Rate_Three, Expected_Two, Expected_Three : Normal_Support.Probability) with
     Global => (In_Out => (Report_Output, Trace)),
     Pre => Trials >= 2 and then Valid (C) and then C.Total = Trials,
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Simulation_Row_Event, Hoeflin_Boundary_Models.Simulation_Payload (N, Trials, Mean, Variance, C, Rate_Two, Rate_Three, Expected_Two, Expected_Three)) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Simulation_Row_Event and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trace.Rows = Trace.Rows'Old + 1,
     Depends => ((Report_Output, Trace) => (N, Trials, Mean, Variance, C, Rate_Two, Rate_Three, Expected_Two, Expected_Three, Report_Output, Trace));
   procedure Calculations_Header with
     Global => (In_Out => (Report_Output, Trace)),
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Calculations_Header_Event, Hoeflin_Boundary_Models.Empty_Payload) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Calculations_Header_Event and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trace.Rows = 0,
     Depends => ((Report_Output, Trace) => (Report_Output, Trace));
   procedure Calculation_Row
     (N : Test_Count; Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value) with
     Global => (In_Out => (Report_Output, Trace)),
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Calculation_Row_Event, Hoeflin_Boundary_Models.Calculation_Payload (N, Factor, Z, Score)) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Calculation_Row_Event and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trace.Rows = Trace.Rows'Old + 1,
     Depends => ((Report_Output, Trace) => (N, Factor, Z, Score, Report_Output, Trace));
   procedure Infinite_Row
     (Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value) with
     Global => (In_Out => (Report_Output, Trace)),
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Infinite_Row_Event, Hoeflin_Boundary_Models.Calculation_Payload (0, Factor, Z, Score)) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Infinite_Row_Event and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trace.Rows = Trace.Rows'Old + 1,
     Depends => ((Report_Output, Trace) => (Factor, Z, Score, Report_Output, Trace));
   procedure Examples_Header with
     Global => (In_Out => (Report_Output, Trace)),
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Examples_Header_Event, Hoeflin_Boundary_Models.Empty_Payload) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Examples_Header_Event and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trace.Rows = 0,
     Depends => ((Report_Output, Trace) => (Report_Output, Trace));
   procedure Example (Label : String; X : Real) with
     Global => (In_Out => (Report_Output, Trace)),
     Post => Trace = Hoeflin_Boundary_Models.Transition (Trace'Old, Hoeflin_Boundary_Models.Example_Event, Hoeflin_Boundary_Models.Example_Payload (Label'Length, X)) and then
       Trace.Last_Event = Hoeflin_Boundary_Models.Example_Event and then
       Trace.Events = Trace.Events'Old + 1 and then
       Trace.Rows = Trace.Rows'Old + 1,
     Depends => ((Report_Output, Trace) => (Label, X, Report_Output, Trace));
end Report_IO;
