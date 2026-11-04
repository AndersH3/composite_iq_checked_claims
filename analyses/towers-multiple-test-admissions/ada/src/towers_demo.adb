with Towers_IO_Models;
with Towers_Engine;
with Towers_IO;
use type Towers_IO_Models.Stage;
procedure Towers_Demo with
     SPARK_Mode,
     Global => (In_Out => (Towers_IO.IO_State, Towers_IO_Models.Last_Receipt)),
     Depends => (Towers_IO.IO_State => Towers_IO.IO_State, Towers_IO_Models.Last_Receipt => Towers_IO.IO_State, null => Towers_IO_Models.Last_Receipt),
     Post => Towers_IO_Models.Last_Receipt.Status = Towers_IO_Models.Normal_Return_Observed and then Towers_IO_Models.Last_Receipt.Requested_Files = 4 and then Towers_IO_Models.Last_Receipt.Requested_Data_Rows = 12
   is
   Trials : constant Towers_Engine.Trial_Count := Towers_IO.Read_Trials;
   Seed : constant Towers_Engine.Seed_Value := Towers_IO.Read_Seed;
   Data : Towers_Engine.Results;
   Trace : Towers_IO_Models.Receipt renames Towers_IO_Models.Last_Receipt;
begin
   Trace.Status := Towers_IO_Models.Empty;
   Towers_IO_Models.Observe_Trials (Trace, Trials);
   Towers_IO_Models.Observe_Seed (Trace, Seed);
   Towers_Engine.Compute (Trials, Seed, Data);
   Towers_IO_Models.Request_Report (Trace, Trials, Seed, Data);
   Towers_IO.Write_Report (Trials, Seed, Data);
   Towers_IO_Models.Observe_Normal_Return (Trace, Data);
   Towers_IO_Models.Check_Completed (Trace);
end Towers_Demo;
